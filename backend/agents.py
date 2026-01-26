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

# 1. THE "SEMANTIC AUDITOR" PROMPT (General Purpose)
# Instead of hardcoding ">= 0", we instruct the AI to use its intelligence
# to determine what "Safety" means for the specific code provided.
TRANSLATOR_PROMPT = """
You are a Literal Code Translator and Security Auditor.

### PHASE 1: LITERAL TRANSLATION (The Mirror)
Translate the Python code to Lean 4 EXACTLY as written.
- **Strict Fidelity:** If the Python code allows a crash, an overflow, or an invalid state, your Lean code MUST allow it too.
- **Do NOT fix bugs.**
- **Do NOT add guardrails** (e.g., `if` checks) that are not in the source.

### PHASE 2: INFERRING SAFETY (The Specification)
Analyze the function names, variable names, and logic to determine the **Implicit Safety Invariant**.
- If the code handles money/quantities -> Invariant is likely `non-negative`.
- If the code handles lists/arrays -> Invariant is likely `in-bounds`.
- If the code handles sorting -> Invariant is `ordered`.

### PHASE 3: VERIFICATION THEOREM
Generate a theorem named `verify_safety` that attempts to prove the **Implicit Safety Invariant** holds.
- **Crucial:** If the Python code fails to enforce the invariant (e.g., allows negative balance), the theorem MUST try to prove it ANYWAY.
- We WANT the proof to fail if the code is buggy.

### EXAMPLES (For reasoning style, not copying):

**Context: Banking**
- Code: `withdraw(balance, amount)` with no checks.
- Inferred Invariant: Balance must remain >= 0.
- Theorem: `theorem verify_safety ... : balance >= 0 -> result >= 0`

**Context: Inventory**
- Code: `ship_items(stock, count)` with no checks.
- Inferred Invariant: Stock must remain >= 0.
- Theorem: `theorem verify_safety ... : stock >= 0 -> result >= 0`

**Context: Access Control**
- Code: `access(user_level)` where 0 is admin.
- Inferred Invariant: High numbers shouldn't access low level features.
- Theorem: `theorem verify_safety ... : input_level >= 0 ...`

---

**Task:** Translate the provided Python code to Lean 4.
- Output ONLY the Lean code.
- Do NOT use 'sorry'.
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
    
    # SAFETY INTERLOCK 1: Empty Response (Fail-Closed)
    if not lean_code or "-- ARGUS_ERROR" in lean_code:
        print(f"[{filename}] Translation failed. Flagging as VULNERABLE.")
        return {
            "filename": filename,
            "status": "VULNERABLE",
            "verified": False,
            "proof": lean_code if lean_code else "-- Error: Model refused to translate.",
            "original_code": original_code,
            "fixed_code": None,
            "logs": ["Model refused to translate code. Treated as Fail-Closed (Vulnerable)."]
        }

    # SAFETY INTERLOCK 2: Missing Theorem (Fail-Closed)
    if "theorem" not in lean_code:
        print(f"[{filename}] No verification theorem found. Flagging as VULNERABLE.")
        return {
            "filename": filename,
            "status": "VULNERABLE",
            "verified": False,
            "proof": lean_code,
            "original_code": original_code,
            "fixed_code": None,
            "logs": ["AI generated function definitions but skipped the verification theorem."]
        }

    # Step 2: Initial Verification
    print(f"[{filename}] Verifying Lean code...")
    result = lean_driver.run_verification(lean_code)
    
    initial_verified = result["verified"]
    logs.append(f"Initial verification result: {initial_verified}")
    
    retries = 0
    max_retries = 3
    
    # Step 3: Self-Healing Loop (Fix Proof Only)
    while not result["verified"] and retries < max_retries:
        retries += 1
        print(f"[{filename}] Verification failed (Attempt {retries}/{max_retries}). Fixing Proof...")
        logs.append(f"Attempt {retries} failed. Error: {result['error_message'][:50]}...")
        
        fix_input = f"Broken Lean Code:\n{lean_code}\n\nCompiler Error:\n{result['error_message']}"
        lean_code = call_gemini(FIXER_PROMPT, fix_input)
        
        print(f"[{filename}] Re-verifying fixed proof...")
        result = lean_driver.run_verification(lean_code)
        logs.append(f"Attempt {retries} result: {result['verified']}")
        
    final_verified = result["verified"]
    
    # Final Status Determination
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