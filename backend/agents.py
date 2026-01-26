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
# Emphasizes LITERAL translation - the Translator must NOT fix bugs in function definitions.
TRANSLATOR_PROMPT = """
You are a Literal Code Translator. Your job is to create a MIRROR of the Python code in Lean 4.

### CRITICAL RULE: NO FIXING BUGS

If Python code is buggy (no guards, allows crashes), your Lean code MUST BE EQUALLY BUGGY.

**LITERAL TRANSLATION EXAMPLES:**

Python (BUGGY - no checks):
```python
def withdraw(balance, amount):
    return balance - amount
```

Lean (MUST also have no checks):
```lean
def withdraw (balance : Int) (amount : Int) : Int :=
  balance - amount
```

❌ WRONG (adding guards that don't exist):
```lean
def withdraw (balance : Int) (amount : Int) : Int :=
  if amount > balance then balance else balance - amount  -- WRONG! Python has no 'if'!
```

---

Python (SECURE - has checks):
```python
def withdraw(balance, amount):
    if amount <= 0:
        return balance
    if amount > balance:
        return balance
    return balance - amount
```

Lean (translate the checks literally):
```lean
def withdraw (balance : Int) (amount : Int) : Int :=
  if amount ≤ 0 then balance
  else if amount > balance then balance
  else balance - amount
```

---

### VERIFICATION THEOREM

After translating the functions, generate a theorem `verify_safety` that tries to prove the result is ≥ 0.

- Only assume starting balance ≥ 0: `(h_bal : balance ≥ 0)`
- Do NOT add hypotheses for guards that don't exist in the Python code
- If the code is buggy, the proof WILL fail (this is correct behavior)

**Theorem Example:**
```lean
theorem verify_safety (balance amount : Int) (h_bal : balance ≥ 0) : 
  withdraw balance amount ≥ 0 := by
  unfold withdraw
  split_ifs <;> omega
```

---

**Output:** Only the Lean code. No markdown, no explanations.
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