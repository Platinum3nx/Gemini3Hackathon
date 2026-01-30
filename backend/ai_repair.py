"""
AI Repair Module - Neuro-Symbolic Repair Loop

This module uses Gemini to generate fixes for vulnerable Python code
based on Lean 4 formal verification error messages.

The repair loop:
1. Receives vulnerable code + Lean error message
2. Asks Gemini to analyze the failure and generate a fix
3. Returns corrected Python code that should pass verification
"""

import os
from dotenv import load_dotenv
import google.generativeai as genai

# Load environment variables
load_dotenv(os.path.join(os.path.dirname(__file__), '../.env'))

# --- CONFIGURATION ---
MODEL_NAME = "gemini-3-pro-preview"

# --- REPAIR PROMPT ---
REPAIR_PROMPT = """You are a Formal Verification Security Engineer.

Your task is to fix vulnerable Python code so that it passes formal verification.

## Context
The code below failed a Lean 4 formal verification proof. The proof was trying to verify that a safety invariant holds (e.g., balance >= 0, no duplicates in list, bounds checking, etc.).

## Vulnerable Python Code
```python
{vulnerable_code}
```

## Lean 4 Error Message
```
{lean_error_message}
```

## Your Task
1. Analyze WHY the proof failed based on the error message
2. Identify what guards or checks are missing
3. Generate a FIXED version of the Python code that:
   - Adds appropriate input validation
   - Ensures the safety invariant holds for ALL possible inputs
   - Preserves the original function signatures
   - Maintains the same overall logic/intent

## Rules
- Return ONLY the raw Python code
- Do NOT include markdown code fences (no ```)
- Do NOT include any explanation or commentary
- Do NOT include phrases like "Here is the fixed code"
- The output should be valid Python that can be saved directly to a .py file

## Common Fix Patterns

### Financial/Numeric Code
- Check that amounts are positive before processing
- Check that withdrawals don't exceed balance
- Return the original balance if operation would violate invariant
- Ensure result >= 0 for balance operations

### List Operations
- Check membership BEFORE adding to avoid duplicates:
  `if item not in my_list: return my_list + [item]`
- Check bounds before accessing by index:
  `if 0 <= index < len(my_list): return my_list[index]`
- Check list is non-empty before operations:
  `if my_list: return operation(my_list)`
- Validate items before removal:
  `if item in my_list: return [x for x in my_list if x != item]`

### Set Operations
- Use set semantics for uniqueness: `set(items)`
- Check membership before add: `if item not in s: s.add(item)`

### String Operations
- Check for empty strings: `if s: process(s)`
- Validate length before slicing: `if len(s) >= n: return s[:n]`

### General Safety
- Null/None checks: `if value is not None:`
- Type validation: `if isinstance(value, expected_type):`
- Bounds validation: `if lower <= value <= upper:`

Generate the fixed Python code now:"""



def generate_fix(vulnerable_code: str, lean_error_message: str) -> str:
    """
    Use Gemini to generate a fixed version of vulnerable Python code.
    
    Args:
        vulnerable_code: The Python code that failed verification
        lean_error_message: The error message from the Lean 4 compiler
        
    Returns:
        Fixed Python code as a string (raw, no markdown)
    """
    # Get API key
    api_key = os.environ.get("GEMINI_API_KEY")
    if not api_key:
        raise ValueError("GEMINI_API_KEY environment variable not set")
    
    # Configure the client
    genai.configure(api_key=api_key)
    
    # Create the model
    model = genai.GenerativeModel(MODEL_NAME)
    
    # Format the prompt
    prompt = REPAIR_PROMPT.format(
        vulnerable_code=vulnerable_code,
        lean_error_message=lean_error_message
    )
    
    # Generate the fix with robust error handling
    print(f"[AI Repair] Asking Gemini ({MODEL_NAME}) to generate a fix...")
    
    try:
        response = model.generate_content(prompt)
    except Exception as e:
        error_str = str(e).lower()
        # Check for 404 / NotFound errors
        if "404" in error_str or "not found" in error_str or "notfound" in error_str:
            print(f"[AI Repair] ERROR: Model '{MODEL_NAME}' not found (404)")
            print("[AI Repair] Listing all available models...")
            try:
                available_models = genai.list_models()
                print("[AI Repair] Available models:")
                for m in available_models:
                    print(f"  - {m.name}")
            except Exception as list_error:
                print(f"[AI Repair] Could not list models: {list_error}")
        # Re-raise the original exception
        raise
    
    # Extract the response text
    fixed_code = response.text.strip()
    
    # Clean up any accidental markdown fences
    if fixed_code.startswith("```python"):
        fixed_code = fixed_code[9:]
    if fixed_code.startswith("```"):
        fixed_code = fixed_code[3:]
    if fixed_code.endswith("```"):
        fixed_code = fixed_code[:-3]
    
    fixed_code = fixed_code.strip()
    
    print("[AI Repair] Fix generated successfully")
    return fixed_code


# --- TEST ---
if __name__ == "__main__":
    # Test with example vulnerable code
    test_code = '''
def withdraw(balance, amount):
    return balance - amount
'''
    
    test_error = '''
verify_test.lean:9:2: error: omega could not prove the goal
balance amount : Int
h_bal : balance ≥ 0
⊢ balance - amount ≥ 0
'''
    
    print("Testing AI Repair...")
    print("=" * 50)
    print("Vulnerable Code:")
    print(test_code)
    print("=" * 50)
    print("Lean Error:")
    print(test_error)
    print("=" * 50)
    
    try:
        fixed = generate_fix(test_code, test_error)
        print("Fixed Code:")
        print(fixed)
    except Exception as e:
        print(f"Error: {e}")
