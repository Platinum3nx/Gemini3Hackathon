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

# 1. THE "DUMB TRANSPILER" PROMPT (The Mirror Strategy)
# This forces the AI to copy bugs literally. If the Python code lacks a check,
# the Lean code must lack it too, so the proof will naturally fail.
TRANSLATOR_PROMPT = """
You are a mechanical, literal transpiler from Python to Lean 4. 
You do NOT understand security. You do NOT fix bugs. Your goal is strict structural preservation.

### RULES:
1. **Preserve Vulnerabilities:** If the Python code subtracts money without an `if` check, your Lean code **MUST** subtract money without an `if` check.
2. **No Guardrails:** Do NOT add `if amount > 0` or `if balance >= amount` unless those exact lines appear in the Python source.
3. **Structure Mapping:**
   - Python `return x - y`  -> Lean `x - y`
   - Python `if x > y:`     -> Lean `if x > y then`
   - **NO OTHER CHANGES ALLOWED.**

### EXAMPLES:

**Input (Python):**
def withdraw(balance, amount):
    # No checks!
    return balance - amount

**BAD Output (Do NOT do this - it fixes the bug):**
def withdraw (b : Int) (a : Int) : Int :=
  if b >= a then b - a else b

**CORRECT Output (Do this):**
def withdraw (b : Int) (a : Int) : Int :=
  b - a  -- Preserves the overdraft bug

---

**Task:** Translate the following Python code to Lean 4. 
Do NOT use 'sorry'. 
Do NOT fix bugs. 
If the code is unsafe, the proof must fail.
"""

# 2. THE "NUCLEAR OPTION" PROMPT (The Auto-Tactic)
# This generic script tries everything (simplify, split, math) in a safe order.
# It works for simple functions AND complex branching without crashing.
FIXER_PROMPT = """
Role: You are an automated proof generator. Output this exact Auto-Tactic script for every theorem.

Instructions:
1. Do NOT try to be clever.
2. Do NOT use `first`, `match`, or complex branching.
3. Just output the script below verbatim.

The Universal Script:
intros
try simp [func_name]
try split
all_goals (
  try intro
  try simp_all
  try omega
)

Goal: This script mechanically attempts to split (if needed) and solves linear arithmetic (omega).
Output: Return ONLY the fixed Lean code block.
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
        
        # Disable safety settings so the model isn't afraid to discuss "vulnerable" code
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

def audit_file(filename: str, code: str) -> dict:
    """
    Audits a single file: Translates to Lean 4, verifies, and attempts to fix if failed.
    Returns a dictionary with the final status and details.
    """
    original_code = code
    current_code = original_code
    logs = []
    
    # Step 1: Initial Translation
    print(f"[{filename}] Translating Python to Lean 4...")
    lean_code = call_gemini(TRANSLATOR_PROMPT, current_code)
    
    # FAIL-CLOSED CHECK:
    # If the AI refuses to translate (due to safety filters or confusion), 
    # we MUST assume the file is dangerous.
    if not lean_code or "-- ARGUS_ERROR" in lean_code:
        print(f"[{filename}] Translation failed. Flagging as VULNERABLE.")
        return {
            "filename": filename,
            "status": "VULNERABLE",
            "verified": False,
            "initial_verified": False,
            "proof": lean_code if lean_code else "-- Error: Model refused to translate.",
            "original_code": original_code,
            "fixed_code": None,
            "logs": ["Model refused to translate code. Treated as Fail-Closed (Vulnerable)."]
        }

    # Step 2: Initial Verification
    print(f"[{filename}] Verifying Lean code...")
    result = lean_driver.run_verification(lean_code)
    
    initial_verified = result["verified"]
    logs.append(f"Initial verification result: {initial_verified}")
    
    retries = 0
    max_retries = 3
    
    # Step 3: Self-Healing Loop
    # We attempt to fix the PROOF, not the python code, to prove validity.
    while not result["verified"] and retries < max_retries:
        retries += 1
        print(f"[{filename}] Verification failed (Attempt {retries}/{max_retries}). Fixing Proof...")
        logs.append(f"Attempt {retries} failed. Error: {result['error_message'][:50]}...")
        
        # Fix (Lean-to-Lean)
        fix_input = f"Broken Lean Code:\n{lean_code}\n\nCompiler Error:\n{result['error_message']}"
        lean_code = call_gemini(FIXER_PROMPT, fix_input)
        
        # Re-verify
        print(f"[{filename}] Re-verifying fixed proof...")
        result = lean_driver.run_verification(lean_code)
        logs.append(f"Attempt {retries} result: {result['verified']}")
        
    final_verified = result["verified"]
    
    # LOGIC:
    # If verified == True, the math proves the code is safe. -> SECURE
    # If verified == False, the math proves the code is unsafe (or broken). -> VULNERABLE
    ui_status = "SECURE" if final_verified else "VULNERABLE"
        
    return {
        "filename": filename,
        "status": ui_status,
        "verified": final_verified,
        "initial_verified": initial_verified,
        "proof": lean_code,
        "original_code": original_code,
        "fixed_code": current_code, 
        "logs": logs
    }