"""
Advanced Python to Lean 4 Translator

This module uses Gemini for intelligent translation of complex Python constructs
to Lean 4, supporting:
- Lists (List[int], List[str])
- Membership checks (x in list)
- List operations (append, concatenation)
- Set operations
- String operations
- Complex invariants (Nodup, sorted, etc.)

The neuro-symbolic approach:
1. Gemini translates Python → Lean (intelligent, handles complex code)
2. Lean 4 verifies the translation is correct (catches hallucinations)
"""

import os
import re
from dotenv import load_dotenv
import google.generativeai as genai
from google.generativeai.types import HarmCategory, HarmBlockThreshold

# Load environment variables
load_dotenv(os.path.join(os.path.dirname(__file__), '../.env'))

# --- CONFIGURATION ---
MODEL_NAME = "gemini-3-pro-preview"

# --- COMPREHENSIVE TRANSLATION PROMPT ---
ADVANCED_TRANSLATION_PROMPT = """You are an expert Python to Lean 4 translator for formal verification.

Your task is to translate Python code into Lean 4 with appropriate safety theorems.

## TRANSLATION RULES

### 1. Type Mappings
| Python Type | Lean 4 Type |
|------------|-------------|
| `int` | `Int` |
| `float` | `Float` (or `Int` for financial code) |
| `str` | `String` |
| `bool` | `Bool` |
| `List[int]` | `List Int` |
| `List[str]` | `List String` |
| `Set[int]` | `Finset Int` or `Set Int` |
| `Dict[K, V]` | `K → Option V` (function type) |
| `Optional[T]` | `Option T` |
| `Tuple[A, B]` | `A × B` |

### 2. Operation Mappings

#### List Operations
| Python | Lean 4 |
|--------|--------|
| `x in my_list` | `x ∈ my_list` or `List.mem x my_list` |
| `x not in my_list` | `x ∉ my_list` or `¬ List.mem x my_list` |
| `my_list + [item]` | `my_list ++ [item]` |
| `my_list.append(item)` | `my_list ++ [item]` (returns new list) |
| `len(my_list)` | `my_list.length` or `List.length my_list` |
| `my_list[i]` | `my_list.get! i` or `my_list[i]!` |
| `my_list[:n]` | `my_list.take n` |
| `my_list[n:]` | `my_list.drop n` |

#### Arithmetic & Comparison
| Python | Lean 4 |
|--------|--------|
| `a + b` | `a + b` |
| `a - b` | `a - b` |
| `a * b` | `a * b` |
| `a / b` | `a / b` (integer) |
| `a % b` | `a % b` |
| `a == b` | `a = b` (in proofs) or `a == b` (decidable) |
| `a != b` | `a ≠ b` |
| `a and b` | `a ∧ b` |
| `a or b` | `a ∨ b` |
| `not a` | `¬a` |

#### Control Flow
| Python | Lean 4 |
|--------|--------|
| `if cond: return x else: return y` | `if cond then x else y` |
| `for x in items: ...` | Use `List.map`, `List.filter`, or recursion |
| `return value` | Just `value` (last expression) |

### 3. Invariant Generation from Comments

When you see comments indicating invariants, generate appropriate theorems:

| Comment Pattern | Lean Theorem |
|----------------|--------------|
| "No duplicates" / "unique" | `List.Nodup result` |
| "sorted" / "in order" | `List.Sorted (· ≤ ·) result` |
| "non-empty" | `result ≠ []` or `result.length > 0` |
| "positive" / "non-negative" | `∀ x ∈ result, x ≥ 0` |
| "balance >= 0" | `result ≥ 0` |
| "within bounds" | Use interval predicates |

### 4. Common Safety Theorems

Generate theorems based on the code's domain:

**Financial/Balance Operations:**
```lean
theorem balance_non_negative (balance amount : Int) (h : balance ≥ 0) :
  withdraw balance amount ≥ 0 := by
  unfold withdraw
  split_ifs <;> omega
```

**List Operations (No Duplicates):**
```lean
theorem add_preserves_nodup (l : List Int) (x : Int) (h_nodup : l.Nodup) (h_not_mem : x ∉ l) :
  (l ++ [x]).Nodup := by
  apply List.Nodup.append h_nodup
  · simp [List.Nodup]
  · simp [List.disjoint_singleton]
    exact h_not_mem
```

**Membership Checks:**
```lean
theorem member_after_add (l : List Int) (x : Int) :
  x ∈ l ++ [x] := by
  simp
```

### 5. Required Imports

Always include these imports at the top:
```lean
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
```

## OUTPUT FORMAT

Return ONLY valid Lean 4 code. Structure:
1. Imports
2. Function definitions (translate all functions)
3. Theorem(s) to verify safety properties

Do NOT include:
- Markdown code fences (no ```)
- Explanatory text
- Comments about what you're doing

## INPUT

Python code to translate:
```python
{python_code}
```

Generate the Lean 4 translation now:"""


# --- INVARIANT DETECTION PROMPT ---
INVARIANT_DETECTION_PROMPT = """Analyze this Python code and identify what safety properties/invariants should be proven.

Python code:
```python
{python_code}
```

Look for:
1. Comments mentioning "no duplicates", "unique", "sorted", "positive", etc.
2. Financial operations (balance should stay >= 0)
3. List operations (membership, bounds, etc.)
4. Null/None checks
5. Type constraints

Return a JSON object with:
{{
  "domain": "financial" | "list_operations" | "string_operations" | "general",
  "invariants": [
    {{"type": "non_negative", "target": "balance", "description": "Balance should never go negative"}},
    ...
  ],
  "suggested_theorems": [
    "theorem name and brief description"
  ]
}}

Return ONLY the JSON, no markdown fences."""


def clean_response(text: str) -> str:
    """Remove markdown code fences from response."""
    text = re.sub(r"^```[a-zA-Z]*\n", "", text, flags=re.MULTILINE)
    text = re.sub(r"```$", "", text, flags=re.MULTILINE)
    return text.strip()


def translate_advanced(python_code: str) -> str:
    """
    Use Gemini to translate complex Python code to Lean 4.
    
    This is the advanced translator that handles:
    - Lists and membership
    - Complex control flow
    - Multiple invariant types
    
    Args:
        python_code: Python source code string
        
    Returns:
        Lean 4 code with functions and theorems
    """
    api_key = os.getenv("GEMINI_API_KEY")
    if not api_key:
        return "-- ERROR: GEMINI_API_KEY not set"
    
    genai.configure(api_key=api_key)
    model = genai.GenerativeModel(MODEL_NAME)
    
    prompt = ADVANCED_TRANSLATION_PROMPT.format(python_code=python_code)
    
    safety_settings = {
        HarmCategory.HARM_CATEGORY_DANGEROUS_CONTENT: HarmBlockThreshold.BLOCK_NONE,
        HarmCategory.HARM_CATEGORY_HATE_SPEECH: HarmBlockThreshold.BLOCK_NONE,
        HarmCategory.HARM_CATEGORY_HARASSMENT: HarmBlockThreshold.BLOCK_NONE,
        HarmCategory.HARM_CATEGORY_SEXUALLY_EXPLICIT: HarmBlockThreshold.BLOCK_NONE,
    }
    
    try:
        print("[Advanced Translator] Translating Python to Lean 4...")
        response = model.generate_content(prompt, safety_settings=safety_settings)
        
        if response.parts:
            lean_code = clean_response(response.text)
            print("[Advanced Translator] Translation complete")
            return lean_code
        else:
            return "-- ERROR: Empty response from Gemini"
            
    except Exception as e:
        print(f"[Advanced Translator] Error: {e}")
        return f"-- ERROR: {e}"


def detect_invariants(python_code: str) -> dict:
    """
    Use Gemini to detect what invariants should be proven for the code.
    
    Args:
        python_code: Python source code string
        
    Returns:
        Dictionary with detected invariants and suggested theorems
    """
    import json
    
    api_key = os.getenv("GEMINI_API_KEY")
    if not api_key:
        return {"error": "GEMINI_API_KEY not set"}
    
    genai.configure(api_key=api_key)
    model = genai.GenerativeModel(MODEL_NAME)
    
    prompt = INVARIANT_DETECTION_PROMPT.format(python_code=python_code)
    
    try:
        response = model.generate_content(prompt)
        if response.parts:
            result = clean_response(response.text)
            return json.loads(result)
        else:
            return {"error": "Empty response"}
    except Exception as e:
        return {"error": str(e)}


# --- QUICK TEST ---
if __name__ == "__main__":
    test_list_code = '''
from typing import List

def add_unique(items: List[int], new_item: int) -> List[int]:
    """Add item only if not already present. No duplicates allowed."""
    if new_item in items:
        return items
    return items + [new_item]

def remove_item(items: List[int], item: int) -> List[int]:
    """Remove item from list if present."""
    return [x for x in items if x != item]
'''
    
    print("=== Testing Advanced Translator ===")
    print("Input Python code:")
    print(test_list_code)
    print("\n" + "="*50 + "\n")
    
    result = translate_advanced(test_list_code)
    print("Generated Lean 4 code:")
    print(result)
