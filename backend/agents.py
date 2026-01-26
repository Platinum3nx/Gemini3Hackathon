from dotenv import load_dotenv
import os
import re
import google.generativeai as genai
from google.generativeai.types import HarmCategory, HarmBlockThreshold

# Load environment variables
load_dotenv(os.path.join(os.path.dirname(__file__), '../.env'))

# --- CONFIGURATION ---
MODEL_NAME = "gemini-3-pro-preview"

# --- PROMPTS ---

# 1. THEOREM GENERATOR PROMPT (Hybrid Approach)
# Functions are translated by AST parser (100% reliable).
# Gemini only generates the verification theorem.
THEOREM_PROMPT = """
You are given Lean 4 function definitions that were translated from Python.

Your task: Generate a theorem `verify_safety` that proves the main function's result is >= 0, assuming the starting balance is >= 0.

Rules:
1. Only assume starting balance is valid: `(h_bal : balance ≥ 0)`
2. Do NOT add extra hypotheses (like `amount <= balance`) - let the proof fail if the code is buggy
3. Use this tactic pattern: `unfold <function_name>; split_ifs <;> omega`

Example output:
```lean
theorem verify_safety (balance amount : Int) (h_bal : balance ≥ 0) : 
  withdraw balance amount ≥ 0 := by
  unfold withdraw
  split_ifs <;> omega
```

Output ONLY the theorem statement and proof. No markdown fences, no explanations.
"""

# 2. THE "NUCLEAR OPTION" PROMPT (Universal Solver)
# This script works for ANY logic that involves integers or control flow.
# It is not specific to wallets.
FIXER_PROMPT = """
Role: You are an automated proof generator. Output this exact Auto-Tactic script for every theorem.

Instructions:
1. Do NOT try to be clever.
2. Do NOT use `first`, `match`, or complex branching.
3. Just output the script below verbatim.

The Universal Script:
  unfold func_name
  split_ifs <;> omega

Alternative (if split_ifs fails):
  simp only [func_name]
  split_ifs
  all_goals omega

Goal: This script unfolds the function, splits all if-then-else branches with split_ifs, and solves linear arithmetic with omega.
Output: Return ONLY the fixed Lean code block with the corrected proof.
"""

TRIAGE_PROMPT = """Role: Senior Security Architect. Task: Identify the top 3 high-risk files. Output Format: Return ONLY the 3 filenames as a JSON list of strings."""

# --- HELPER FUNCTIONS ---

def clean_response(text: str) -> str:
    """
    Removes Markdown code fences from the LLM response.
    """
    text = re.sub(r"^```[a-zA-Z]*\n", "", text, flags=re.MULTILINE)
    text = re.sub(r"```$", "", text, flags=re.MULTILINE)
    return text.strip()

def call_gemini(prompt_template: str, content: str) -> str:
    try:
        api_key = os.getenv("GEMINI_API_KEY")
        if not api_key:
            return "-- ARGUS_ERROR: GEMINI_API_KEY not found."

        genai.configure(api_key=api_key)
        model = genai.GenerativeModel(MODEL_NAME)
        
        user_content = f"{prompt_template}\n\nUser Input:\n{content}"
        
        safety_settings = {
            HarmCategory.HARM_CATEGORY_DANGEROUS_CONTENT: HarmBlockThreshold.BLOCK_NONE,
            HarmCategory.HARM_CATEGORY_HATE_SPEECH: HarmBlockThreshold.BLOCK_NONE,
            HarmCategory.HARM_CATEGORY_HARASSMENT: HarmBlockThreshold.BLOCK_NONE,
            HarmCategory.HARM_CATEGORY_SEXUALLY_EXPLICIT: HarmBlockThreshold.BLOCK_NONE,
        }

        response = model.generate_content(user_content, safety_settings=safety_settings)

        if response.parts:
            return clean_response(response.text)
        else:
            return "-- ARGUS_ERROR: Empty response."

    except Exception as e:
        print(f"Gemini API Error: {e}")
        return f"-- ARGUS_ERROR: {e}"

def triage_files(file_list: list[str]) -> list[str]:
    import json
    content = f"Files: {json.dumps(file_list)}\n\nIdentify top 3 high-risk files."
    response_text = call_gemini(TRIAGE_PROMPT, content)
    try:
        return json.loads(response_text)
    except json.JSONDecodeError:
        print(f"Error parsing triage: {response_text}")
        return []

# --- MAIN AUDIT LOGIC ---

from . import lean_driver
from . import python_to_lean

def audit_file(filename: str, code: str) -> dict:
    """
    Audits a single file using the HYBRID approach:
    1. AST Parser translates Python -> Lean functions (100% reliable)
    2. Gemini generates the verification theorem only
    3. Lean compiler proves or disproves the theorem
    
    Returns a dictionary with the final status and details.
    """
    original_code = code
    logs = []
    
    # Step 1: AST-based Translation (100% reliable)
    print(f"[{filename}] Step 1: AST Translation (Python -> Lean functions)...")
    lean_functions = python_to_lean.translate_python_to_lean(code)
    logs.append("AST translation completed")
    
    # Check for parse errors
    if lean_functions.startswith("-- PARSE_ERROR"):
        print(f"[{filename}] Python parse error. Flagging as VULNERABLE.")
        return {
            "filename": filename,
            "status": "VULNERABLE",
            "verified": False,
            "proof": lean_functions,
            "original_code": original_code,
            "fixed_code": None,
            "logs": ["Python code has syntax errors and could not be parsed."]
        }
    
    # Step 2: Gemini generates theorem only
    print(f"[{filename}] Step 2: Gemini generating verification theorem...")
    theorem_input = f"Lean function definitions:\n\n{lean_functions}"
    theorem_code = call_gemini(THEOREM_PROMPT, theorem_input)
    logs.append("Theorem generation completed")
    
    # Clean up theorem (remove markdown if present)
    theorem_code = clean_response(theorem_code)
    
    # Combine functions + theorem
    lean_code = f"{lean_functions}\n\n{theorem_code}"
    
    # SAFETY INTERLOCK: Missing theorem
    if "theorem" not in lean_code:
        print(f"[{filename}] No theorem generated. Flagging as VULNERABLE.")
        return {
            "filename": filename,
            "status": "VULNERABLE", 
            "verified": False,
            "proof": lean_code,
            "original_code": original_code,
            "fixed_code": None,
            "logs": ["Gemini failed to generate verification theorem."]
        }
    
    # Step 3: Verification
    print(f"[{filename}] Step 3: Running Lean verification...")
    result = lean_driver.run_verification(lean_code)
    
    initial_verified = result["verified"]
    logs.append(f"Initial verification: {'PASSED' if initial_verified else 'FAILED'}")
    
    retries = 0
    max_retries = 3
    
    # Step 4: Self-Healing Loop (fix proof tactics only, not functions)
    while not result["verified"] and retries < max_retries:
        retries += 1
        print(f"[{filename}] Proof failed. Attempt {retries}/{max_retries} to fix tactics...")
        logs.append(f"Fix attempt {retries}: {result['error_message'][:50]}...")
        
        # Ask Gemini to fix the proof tactics (NOT the functions)
        fix_input = f"Lean Code (DO NOT CHANGE THE FUNCTION DEFINITIONS):\n{lean_code}\n\nCompiler Error:\n{result['error_message']}"
        fixed_code = call_gemini(FIXER_PROMPT, fix_input)
        fixed_code = clean_response(fixed_code)
        
        # If the fix is just tactics, append to original functions
        if "def " not in fixed_code and "theorem" in fixed_code:
            lean_code = f"{lean_functions}\n\n{fixed_code}"
        else:
            lean_code = fixed_code
        
        print(f"[{filename}] Re-verifying...")
        result = lean_driver.run_verification(lean_code)
        logs.append(f"Attempt {retries}: {'PASSED' if result['verified'] else 'FAILED'}")
    
    final_verified = result["verified"]
    ui_status = "SECURE" if final_verified else "VULNERABLE"
    
    print(f"[{filename}] Final status: {ui_status}")
    
    return {
        "filename": filename,
        "status": ui_status,
        "verified": final_verified,
        "initial_verified": initial_verified,
        "proof": lean_code,
        "original_code": original_code,
        "fixed_code": original_code,  # We don't modify Python in hybrid mode
        "logs": logs
    }