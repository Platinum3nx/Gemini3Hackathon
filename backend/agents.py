from dotenv import load_dotenv
import os
import google.generativeai as genai

# Load environment variables from the root directory
load_dotenv(os.path.join(os.path.dirname(__file__), '../.env'))

# --- 1. THE TRANSLATOR (TRANSLATOR_PROMPT) ---
TRANSLATOR_PROMPT = """Role: Expert Formal Verification Engineer.

Task: Translate Python code into a valid Lean 4 theorem.

Constraint: You must use import Mathlib at the top.

Constraint: For the proof block (:= by ...), start simple. Use tactics like simp, arith, or induction if needed.

Output Format: Return only the Lean code block (no markdown ticks if possible, or strip them)."""

# --- 2. THE FIXER (FIXER_PROMPT) ---
FIXER_PROMPT = """Role: Senior Security Auditor.

Task: Fix the Python code based on a mathematical error.

Input: You will receive the 'Original Python Code' and the 'Lean Error Message'.

Strategy: Analyze the error (e.g., 'division by zero', 'index out of bounds'). Rewrite the Python code to handle that edge case (e.g., add an if check).

Output Format: Return only the corrected Python code."""

# --- 3. THE TRIAGE AGENT (TRIAGE_PROMPT) ---
TRIAGE_PROMPT = """Role: Senior Security Architect.

Task: Given a list of filenames, identify the 3 files that are most critical for security, financial logic, or authentication.

Output Format: Return ONLY the 3 filenames as a JSON list of strings. Do not include markdown code blocks."""

MODEL_NAME = "gemini-3-flash-preview"

def triage_files(file_list: list[str]) -> list[str]:
    """
    Calls the Gemini API to identify critical files.
    """
    import json
    
    content = f"Here is the list of files in the repository:\n{json.dumps(file_list)}\n\nPlease identify the top 3 high-risk files."
    
    response_text = call_gemini(TRIAGE_PROMPT, content)
    
    try:
        # Strip potential markdown formatting
        cleaned_text = response_text.replace("```json", "").replace("```", "").strip()
        return json.loads(cleaned_text)
    except json.JSONDecodeError:
        print(f"Error parsing triage response: {response_text}")
        return []

def call_gemini(system_prompt: str, user_content: str) -> str:
    """
    Calls the Gemini API with a system prompt and user content.
    
    Args:
        system_prompt: The system instruction for the agent.
        user_content: The user's input (code or error message).
        
    Returns:
        The text response from the model.
    """
    api_key = os.environ.get("GEMINI_API_KEY")
    if not api_key:
        raise ValueError("GEMINI_API_KEY environment variable not set")
        
    genai.configure(api_key=api_key)
    
    model = genai.GenerativeModel(
        model_name=MODEL_NAME,
        system_instruction=system_prompt
    )
    
    response = model.generate_content(user_content)
    return response.text
