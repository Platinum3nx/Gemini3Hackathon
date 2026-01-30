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
from . import advanced_translator

def _is_complex_code(code: str) -> bool:
    """
    Detect if Python code requires the advanced (LLM-based) translator.
    
    Returns True if code contains:
    - List type hints or operations
    - Set operations
    - Complex data structures
    - List comprehensions
    """
    complex_patterns = [
        "List[",           # Type hints: List[int], List[str]
        "Set[",            # Set type hints
        "Dict[",           # Dictionary type hints
        " in ",            # Membership checks
        ".append(",        # List append
        ".extend(",        # List extend
        ".remove(",        # List/set remove
        ".add(",           # Set add
        " for ",           # Comprehensions or loops
        "Optional[",       # Optional type hints
        "Tuple[",          # Tuple type hints
        "sorted(",         # Sorted operations
        "filter(",         # Filter operations
        "map(",            # Map operations
        "# No duplicates", # Invariant comments
        "# unique",
        "# sorted",
        "# non-empty",
    ]
    
    code_lower = code.lower()
    for pattern in complex_patterns:
        if pattern.lower() in code_lower:
            return True
    
    return False


def audit_file(filename: str, code: str) -> dict:
    """
    Audits a single file using hybrid translation:
    
    1. Simple code (arithmetic): Uses deterministic AST translator
    2. Complex code (lists, sets): Uses Gemini-powered advanced translator
    3. Lean compiler verifies the translation
    4. If verification finds sorry, try tactic substitution
    
    The neuro-symbolic approach ensures AI translations are mathematically verified.
    
    Returns a dictionary with the final status and details.
    """
    original_code = code
    logs = []
    
    # Determine which translator to use
    use_advanced = _is_complex_code(code)
    
    if use_advanced:
        # Use advanced Gemini-powered translator for complex code
        print(f"[{filename}] Step 1: Advanced translation (Complex Python → Lean)...")
        print(f"[{filename}] Detected: Lists, membership, or complex operations")
        lean_code = advanced_translator.translate_advanced(code)
        logs.append("Advanced (LLM-based) translation for complex code")
    else:
        # Use simple deterministic translator for basic arithmetic
        print(f"[{filename}] Step 1: Deterministic translation (Python → Lean)...")
        lean_code = python_to_lean.translate_with_theorem(code)
        logs.append("Deterministic translation completed (functions + theorem)")
    
    # Check for translation errors
    if lean_code.startswith("-- PARSE_ERROR") or lean_code.startswith("-- ERROR"):
        print(f"[{filename}] Translation error. Flagging as VULNERABLE.")
        return {
            "filename": filename,
            "status": "VULNERABLE",
            "verified": False,
            "proof": lean_code,
            "original_code": original_code,
            "fixed_code": None,
            "logs": ["Code could not be translated to Lean."]
        }
    
    # Step 2: Verification
    print(f"[{filename}] Step 2: Running Lean verification...")
    result = lean_driver.run_verification(lean_code)
    
    initial_verified = result["verified"]
    has_sorry = result.get("has_sorry", False)
    
    # If failed due to sorry, try tactic substitution
    if not initial_verified and has_sorry:
        print(f"[{filename}] Step 2b: Attempting tactic substitution (removing sorry)...")
        logs.append("Initial proof contained 'sorry', attempting tactic substitution")
        
        # Try common tactic replacements for sorry
        tactic_substitutions = [
            ("sorry", "decide"),
            ("sorry", "native_decide"),
            ("sorry", "trivial"),
            ("sorry", "rfl"),
            ("sorry", "simp"),
        ]
        
        for old_tactic, new_tactic in tactic_substitutions:
            modified_code = lean_code.replace(old_tactic, new_tactic)
            if modified_code != lean_code:
                print(f"[{filename}] Trying: {old_tactic} → {new_tactic}")
                retry_result = lean_driver.run_verification(modified_code)
                if retry_result["verified"]:
                    print(f"[{filename}] ✅ Tactic substitution succeeded: {new_tactic}")
                    logs.append(f"Tactic substitution succeeded: {old_tactic} → {new_tactic}")
                    result = retry_result
                    lean_code = modified_code
                    initial_verified = True
                    break
    
    logs.append(f"Verification: {'PASSED' if initial_verified else 'FAILED'}")
    
    if not initial_verified and result.get("error_message"):
        logs.append(f"Error: {result['error_message'][:100]}...")
    
    # Simple decision: proof passes = SECURE, proof fails = VULNERABLE
    # NO FIXER, NO RETRIES - this ensures buggy code stays VULNERABLE
    ui_status = "SECURE" if initial_verified else "VULNERABLE"
    
    print(f"[{filename}] Final status: {ui_status}")
    
    return {
        "filename": filename,
        "status": ui_status,
        "verified": initial_verified,
        "proof": lean_code,
        "original_code": original_code,
        "logs": logs
    }