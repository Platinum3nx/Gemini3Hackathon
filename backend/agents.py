from dotenv import load_dotenv
import os
import re
import google.generativeai as genai
from google.generativeai.types import HarmCategory, HarmBlockThreshold

# Load environment variables
load_dotenv(os.path.join(os.path.dirname(__file__), '../.env'))

# --- PROMPTS ---
TRANSLATOR_PROMPT = """Role: You are a Literal Code Translator. Your goal is to map Python logic 1:1 to Lean 4.

Task: Translate Python code into a valid Lean 4 theorem.

UNIVERSAL CONSTRAINT 1 (The Mirror Rule):

Translate the control flow EXACTLY as written.

If the Python code contains a check (e.g., `if x > 0:`), you MUST include it.

If the Python code OMITS a check (e.g., it allows negative inputs), your Lean translation MUST also allow them.

Do NOT "fix" bugs. Do NOT add safety checks that are not in the source.

UNIVERSAL CONSTRAINT 2 (Theorem Fidelity):

When generating verification theorems, do NOT add "validity assumptions" (preconditions) unless the code explicitly enforces them.

Example: If a function `f(x)` does not check if `x > 0`, your theorem must attempt to prove safety for ALL x. Do not add `x > 0 -> ...` unless the code checks it.

If the code is unsafe, we WANT the proof to fail.

TECHNICAL CONSTRAINTS:
1. **NO MATHLIB:** Do NOT import Mathlib. Use only standard Lean 4.
2. **USE 'omega':** For all integer arithmetic and inequalities, use the `omega` tactic.
3. **CONTROL FLOW:** For if/else, use `split`. Pattern: `next => intros; simp; omega`.
4. **TRANSLATION PATTERN:**
   - **Classes:** Translate Python classes into a Lean `structure`.
   - **Methods:** Translate methods into functions that take the structure as input and return a new structure.
   - **Invariants:** Write a theorem checking that a specific property holds.
5. **NO FLOATS:** Convert all Python floats to Ints for verification.
6. **OPTION/ERROR HANDLING:** If Python raises an error, translate to `Option T` (return `none` on error).

CRITICAL CONSTRAINT (NO SORRY):

You must NEVER use the keyword `sorry` or `admit` in your output.

If the Python code is buggy (e.g., missing an overflow check), you must write a valid theorem (e.g., `balance >= 0`) and attempt to prove it using standard tactics (`omega`, `simp`).

DO NOT try to "fix" the proof by using `sorry`.

We WANT the verification to fail if the code is unsafe.

A failed proof is a successful audit. A `sorry` proof is a failed audit.

Output Format: Return ONLY the raw Lean code. """

FIXER_PROMPT = """Role: You are a mechanical proof generator. Do NOT use the first tactic. Do NOT use match cases. Do NOT try to be clever.

Input: You receive Broken Code and a Compiler Error.

CRITICAL: You must NOT define new inductive types, structures, or List recursive proofs (like foldl or induction) unless they are explicitly in the Python code. ONLY verify the functions present in the input.

The Only Allowed Script:

For EVERY theorem, you must output EXACTLY this script, verbatim:

Lean

intros
try simp [func_name]
try split
all_goals (
  try intro
  try simp_all
  try omega
)

Explanation: This script uses try to safely attempt splitting. It works for Option types, if/else, and simple functions equally well. Just output it.

Output: Return ONLY the fixed Lean code block."""

TRIAGE_PROMPT = """Role: Senior Security Architect. Task: Identify the top 3 high-risk files. Output Format: Return ONLY the 3 filenames as a JSON list of strings."""

MODEL_NAME = "gemini-3-pro-preview"

def clean_response(text: str) -> str:
    """
    Removes Markdown code fences from the LLM response.
    """
    text = re.sub(r"^```[a-zA-Z]*\n", "", text, flags=re.MULTILINE)
    text = re.sub(r"```$", "", text, flags=re.MULTILINE)
    return text.strip()

def triage_files(file_list: list[str]) -> list[str]:
    import json
    content = f"Files: {json.dumps(file_list)}\n\nIdentify top 3 high-risk files."
    response_text = call_gemini(TRIAGE_PROMPT, content)
    try:
        return json.loads(response_text)
    except json.JSONDecodeError:
        print(f"Error parsing triage: {response_text}")
        return []

def call_gemini(prompt_template: str, content: str) -> str:
    try:
        api_key = os.getenv("GEMINI_API_KEY")
        if not api_key:
            return "-- Error: GEMINI_API_KEY not found."

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
        return f"-- Error: {e}"

from . import lean_driver

def audit_file(filename: str, code: str) -> dict:
    """
    Audits a single file: Translates to Lean 4, verifies, and attempts to fix if failed.
    Returns a dictionary with the final status and details.
    """
    original_code = code
    current_code = original_code
    
    # Step 1: Initial Translation
    print(f"[{filename}] Translating Python to Lean 4...")
    lean_code = call_gemini(TRANSLATOR_PROMPT, current_code)
    
    # Step 2: Initial Verification
    print(f"[{filename}] Verifying Lean code...")
    result = lean_driver.run_verification(lean_code)
    
    initial_verified = result["verified"]
    logs = [f"Initial verification result: {initial_verified}"]
    
    retries = 0
    max_retries = 3
    
    # Step 3: Self-Healing Loop
    while not result["verified"] and retries < max_retries:
        retries += 1
        print(f"[{filename}] Verification failed (Attempt {retries}/{max_retries}). Fixing...")
        logs.append(f"Attempt {retries} failed. Error: {result['error_message'][:50]}...")
        
        # Fix (Lean-to-Lean)
        fix_input = f"Broken Lean Code:\n{lean_code}\n\nCompiler Error:\n{result['error_message']}"
        lean_code = call_gemini(FIXER_PROMPT, fix_input)
        
        # NOTE: We skip re-translation because the fixer now repairs the PROOF, not the Python source.
        # This resolves the 'brittle prompt' issue where converting simple logic errors back to Python is hard.
        
        # Re-verify
        print(f"[{filename}] Re-verifying fixed proof...")
        result = lean_driver.run_verification(lean_code)
        logs.append(f"Attempt {retries} result: {result['verified']}")
        
    final_verified = result["verified"]
    status = "verified" if final_verified else "failed"
    
    ui_status = "VULNERABLE"
    if final_verified:
        ui_status = "SECURE"
        
    return {
        "filename": filename,
        "status": ui_status,
        "verified": final_verified,
        "initial_verified": initial_verified,
        "proof": lean_code,
        "original_code": original_code,
        "fixed_code": current_code, # This remains the Python code (unmodified if we only fixed the proof)
        "logs": logs
    }