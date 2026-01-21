from dotenv import load_dotenv
import os
import re
import google.generativeai as genai
from google.generativeai.types import HarmCategory, HarmBlockThreshold

# Load environment variables
load_dotenv(os.path.join(os.path.dirname(__file__), '../.env'))

# --- PROMPTS ---
TRANSLATOR_PROMPT = """Role: Expert Formal Verification Engineer.

Task: Translate Python code into a valid Lean 4 theorem and proof.

CRITICAL CONSTRAINTS:
1. **DO NOT IMPORT MATHLIB.** Mathlib is NOT installed. Use only standard Lean 4.
2. **USE THE `omega` TACTIC.** For integer arithmetic, use `omega`. Do NOT use `linarith`.
3. **SELF-CONTAINED:** Define simple structures. No external dependencies.
4. **Mocking:** Mock external calls (APIs, DBs) as 'opaque' definitions.

Output Format: Return ONLY the raw Lean code. Do not use Markdown blocks."""

FIXER_PROMPT = """Role: Senior Security Auditor.
Task: Fix the Python code based on a mathematical error.
Output Format: Return ONLY the raw corrected Python code. Do not use Markdown blocks."""

TRIAGE_PROMPT = """Role: Senior Security Architect.
Task: Identify the top 3 high-risk files.
Output Format: Return ONLY the 3 filenames as a JSON list of strings."""

MODEL_NAME = "gemini-2.0-flash-exp"

def clean_response(text: str) -> str:
    """
    Removes Markdown code fences (```lean ... ```) from the LLM response.
    """
    # Remove ```lean, ```python, ```json, or just ```
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
            # --- THE FIX: CLEAN THE TEXT BEFORE RETURNING ---
            return clean_response(response.text)
        else:
            return "-- ARGUS_ERROR: Empty response."

    except Exception as e:
        print(f"Gemini API Error: {e}")
        return f"-- Error: {e}"