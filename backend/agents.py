from dotenv import load_dotenv
import os
import re
import google.generativeai as genai
from google.generativeai.types import HarmCategory, HarmBlockThreshold

# Load environment variables
load_dotenv(os.path.join(os.path.dirname(__file__), '../.env'))

# --- PROMPTS ---
TRANSLATOR_PROMPT = """Role: Expert Formal Verification Engineer.

Task: Translate Python code into a valid Lean 4 theorem.

CRITICAL CONSTRAINTS:
1. **NO MATHLIB:** Do NOT import Mathlib. Use only standard Lean 4.
2. **USE 'omega':** For all integer arithmetic and inequalities, use the `omega` tactic.
3. **CONTROL FLOW & SIMPLIFICATION:**

For if/else, use `split`.

CRITICAL: Inside every `next` branch, you MUST run `simp` or `dsimp` before `omega`.

Pattern: `next => intros; simp; omega` (or `assumption`).

4. **TRANSLATION PATTERN (Apply this pattern to ANY code):**
   - **Classes:** Translate Python classes into a Lean `structure`.
   - **Methods:** Translate methods into functions that take the structure as input and return a new structure.
   - **Invariants:** Write a theorem checking that a specific property holds (e.g., "value never negative").

   **GENERIC SYNTAX EXAMPLE (Do not copy, just follow the style):**
   ```lean
   structure State where
     val : Int

   def update (s : State) (delta : Int) : State :=
     if delta > 0 then { val := s.val + delta } else s

   theorem update_safe (s : State) (delta : Int) :
     s.val >= 0 -> delta > 0 -> (update s delta).val >= 0 := by
     intros h1 h2
     simp [update]
     split
     next => intros; simp; omega  -- 'intros' captures the if-condition
     next => intros; assumption   -- 'intros' captures the else-condition

   -- Example for Option Types:
   def safe_div (a b : Int) : Option Int :=
     if b == 0 then none else some (a / b)
   theorem safe_div_safe (a b : Int) :
     a >= 0 -> b > 0 ->
     match safe_div a b with
     | some res => res >= 0
     | none => True := by
     intros h1 h2
     simp [safe_div]
     split
     next => intros; trivial      -- Handle error case
     next => intros; simp; omega  -- Handle success case
   ```
5. **ADAPTATION: Apply the pattern above to the User's specific Python code.

6. **NO FLOATS: Convert all Python floats to Ints for verification.

7. **DIRECT PROOFS:** Do NOT write theorems that end in -> True. You must prove the inequality directly (e.g., new_state.val >= 0).

8. **OPTION/ERROR HANDLING:**

If the Python code raises an error, translate the return type to `Option T` (return `none` on error).

CRITICAL: When proving theorems about Option types, you MUST use a `match` statement.

Pattern:
```lean
match func_call args with
| some val => val >= 0  -- Prove safety of the value
| none => True          -- Errors are considered safe/handled
```
Do NOT use `Option.getD`, `Option.isSome`, or `exists` logic. Keep it simple.

Output Format: Return ONLY the raw Lean code. """

FIXER_PROMPT = """Role: You are an expert Lean 4 Repair Agent.

Input: You receive Broken Code and a Compiler Error.

The Toolbox (Heuristics):
1. IF error involves if/else: -> Strategy: Use `split`. CRITICAL SYNTAX: `next => intro h; simp_all; omega`. Do NOT use `next h =>`.
2. IF error involves Option types: -> Strategy: `simp [func_name]; split`. Followed by `next => intro h; simp_all`.
3. IF error involves Prod / × / Tuples: -> Strategy: Do NOT use .fst or .snd in proofs. Use `cases` to decompose the tuple (e.g., `cases res with val flag`).
4. IF generic math failure: -> Strategy: Always prefer `simp_all` over `simp`. Try `simp_all` and `omega`.

Output: Return ONLY the fixed Lean code block."""

TRIAGE_PROMPT = """Role: Senior Security Architect. Task: Identify the top 3 high-risk files. Output Format: Return ONLY the 3 filenames as a JSON list of strings."""

MODEL_NAME = "gemini-2.0-flash-exp"

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