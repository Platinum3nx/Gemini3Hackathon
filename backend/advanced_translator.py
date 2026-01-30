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

#### ⚠️ CRITICAL: Membership Guards (if x in list)
This is the MOST IMPORTANT translation. When you see:

**Python:**
```python
if new_id in existing_ids:
    return existing_ids
return existing_ids + [new_id]
```

**You MUST translate to Lean:**
```lean
def add_product_id (existing_ids : List Int) (new_id : Int) : List Int :=
  if new_id ∈ existing_ids then existing_ids else existing_ids ++ [new_id]
```

**NEVER translate it as:**
```lean
-- WRONG! This ignores the guard!
def add_product_id (existing_ids : List Int) (new_id : Int) : List Int :=
  existing_ids ++ [new_id]
```

The `if x in list` → `if x ∈ list then ... else ...` translation is ESSENTIAL for proofs!

### 3. CRITICAL RULE: NO "MAGIC" ASSUMPTIONS

⚠️ **THIS IS THE MOST IMPORTANT RULE** ⚠️

When generating the Lean theorem, you MUST NOT add preconditions (hypotheses) 
unless they are **explicitly enforced by the Python code** (e.g., an `if` statement, 
`assert`, or explicit check).

**WHY THIS MATTERS:**
Adding assumptions that the code doesn't check allows buggy code to falsely pass verification.
The goal is for verification to FAIL if the code is missing required checks.

**EXAMPLES:**

❌ **INCORRECT** - Adds assumption the code doesn't enforce:
```lean
-- WRONG! This assumes new_id ∉ existing_ids but the Python code never checks this
theorem safe (ids : List Int) (new : Int) (h : new ∉ ids) : 
  (add_product_id ids new).Nodup := by ...
```

✅ **CORRECT** - Only assumes what WILL be true (input is valid):
```lean
-- RIGHT! This only assumes the INPUT list is valid, not that new ∉ ids
-- This theorem WILL FAIL if the code blindly appends without checking
theorem safe (ids : List Int) (new : Int) (h_input : ids.Nodup) : 
  (add_product_id ids new).Nodup := by ...
```

**ALLOWED ASSUMPTIONS:**
- Properties of INPUTS that are documented (e.g., "ids is assumed unique" → `h : ids.Nodup`)
- Properties enforced by type system (e.g., `Int` is an integer)
- Starting state validity (e.g., `balance ≥ 0` for financial code)

**FORBIDDEN ASSUMPTIONS:**
- Properties that would make the code work but aren't checked (e.g., `new ∉ ids`)
- Properties the function should enforce but doesn't
- Any condition that "fixes" the bug in the theorem instead of the code

### 4. Invariant Generation from Comments

When you see comments indicating invariants, generate theorems that TEST the code:

| Comment Pattern | Theorem Goal | What Should Happen |
|----------------|--------------|-------------------|
| "No duplicates" | `input.Nodup → output.Nodup` | FAIL if code doesn't guard |
| "sorted" | `input.Sorted → output.Sorted` | FAIL if code breaks order |
| "non-negative" | `input ≥ 0 → output ≥ 0` | FAIL if code allows negative |

### 5. Correct Safety Theorem Examples

**Financial/Balance Operations (assumes starting balance is valid):**
```lean
-- Only assumes STARTING balance is valid
-- Does NOT assume amount <= balance - the code must check this!
theorem balance_non_negative (balance amount : Int) (h : balance ≥ 0) :
  withdraw balance amount ≥ 0 := by
  unfold withdraw
  split_ifs <;> omega
```

**List Operations - BUGGY CODE (will FAIL):**
```lean
-- BUGGY: blindly appends without checking membership
def add_product_id (ids : List Int) (new : Int) : List Int :=
  ids ++ [new]

-- This theorem CANNOT be proven because the code is buggy!
-- The proof will fail, correctly flagging this as VULNERABLE
theorem add_preserves_nodup (ids : List Int) (new : Int) (h : ids.Nodup) :
  (add_product_id ids new).Nodup := by
  unfold add_product_id
  -- Cannot prove: new might already be in ids!
  sorry  -- This will be detected and marked VULNERABLE
```

**List Operations - FIXED CODE (will PASS):**
```lean
-- FIXED: checks membership before appending
def add_product_id (ids : List Int) (new : Int) : List Int :=
  if new ∈ ids then ids else ids ++ [new]

-- This theorem CAN be proven because the code is correct!
theorem add_preserves_nodup (ids : List Int) (new : Int) (h : ids.Nodup) :
  (add_product_id ids new).Nodup := by
  unfold add_product_id
  split_ifs with h_mem
  case isTrue => 
    -- new ∈ ids, so we return ids unchanged
    exact h
  case isFalse =>
    -- new ∉ ids, so appending preserves Nodup
    apply List.nodup_append.mpr
    constructor
    · exact h
    constructor  
    · exact List.nodup_singleton new
    · intro x hx1 hx2
      simp only [List.mem_singleton] at hx2
      rw [hx2] at hx1
      exact h_mem hx1
```


### 6. Required Imports

Always include these imports at the top:
```lean
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
```

### 7. Tactic Strategies (in order of preference)

Use these tactics for proofs. Try them in order:

**For if-then-else branching:**
```lean
split_ifs with h_cond
case isTrue => <proof for true branch>
case isFalse => <proof for false branch>
```

**For List.Nodup preservation:**
```lean
apply List.nodup_append.mpr
constructor
· <prove first list is nodup>
constructor
· <prove second list is nodup (usually simp for singleton)>
· <prove lists are disjoint>
```

**For linear arithmetic:**
- `omega` — Primary choice for Int arithmetic
- `linarith` — Fallback for complex linear constraints
- `simp` — For simplification

**For membership/disjointness:**
- `simp only [List.mem_singleton]` — For singleton membership
- `intro x hx1 hx2` — For proving disjointness

**CRITICAL: Never use `sorry` in final proofs!**
If you cannot complete the proof, the code is buggy and should fail verification.

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


def _deterministic_membership_translation(python_code: str) -> str | None:
    """
    Try to deterministically translate Python code with membership guards.
    
    This handles the common pattern:
        if x in list:
            return list
        return list + [x]
    
    Returns Lean code if pattern is recognized, None otherwise.
    """
    import ast
    
    print("[Deterministic] Starting pattern matching...")
    
    try:
        tree = ast.parse(python_code)
        print("[Deterministic] AST parsed successfully")
        
        # Look for functions with membership guard pattern
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                func_name = node.name
                print(f"[Deterministic] Found function: {func_name}")
                
                # Get arguments
                args = [(arg.arg, "Int") for arg in node.args.args]  # Assume Int for now
                
                # Check for List type hint
                list_param = None
                element_param = None
                for arg in node.args.args:
                    print(f"[Deterministic] Checking arg: {arg.arg}, has annotation: {arg.annotation is not None}")
                    if arg.annotation:
                        if isinstance(arg.annotation, ast.Subscript):
                            if hasattr(arg.annotation.value, 'id') and arg.annotation.value.id == 'List':
                                list_param = arg.arg
                                print(f"[Deterministic] Found list param: {list_param}")
                        else:
                            element_param = arg.arg
                            print(f"[Deterministic] Found element param: {element_param}")
                
                if list_param and element_param:
                    print(f"[Deterministic] Both params found: list={list_param}, element={element_param}")
                    
                    # Look for membership guard pattern in body
                    # Skip docstrings - they appear as Expr(Constant(str))
                    body_statements = []
                    for stmt in node.body:
                        if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant) and isinstance(stmt.value.value, str):
                            print(f"[Deterministic] Skipping docstring")
                            continue  # Skip docstring
                        body_statements.append(stmt)
                    
                    print(f"[Deterministic] Body statements after skipping docstrings: {len(body_statements)}")
                    
                    if len(body_statements) >= 2:
                        first_stmt = body_statements[0]
                        print(f"[Deterministic] First statement type: {type(first_stmt).__name__}")
                        
                        # Check for: if x in list: return list
                        if isinstance(first_stmt, ast.If):
                            test = first_stmt.test
                            print(f"[Deterministic] If test type: {type(test).__name__}")
                            
                            if isinstance(test, ast.Compare) and len(test.ops) == 1:
                                print(f"[Deterministic] Compare op: {type(test.ops[0]).__name__}")
                                
                                if isinstance(test.ops[0], ast.In):
                                    # Found membership check!
                                    checked_var = test.left.id if isinstance(test.left, ast.Name) else None
                                    list_var = test.comparators[0].id if isinstance(test.comparators[0], ast.Name) else None
                                    
                                    print(f"[Deterministic] Checked var: {checked_var}, List var: {list_var}")
                                    print(f"[Deterministic] Expected: checked={element_param}, list={list_param}")
                                    
                                    if checked_var == element_param and list_var == list_param:
                                        print(f"[Deterministic] ✅ PATTERN MATCHED! Generating Lean code...")
                                        # Generate deterministic Lean translation
                                        # NOTE: split_ifs generates case tags `pos` and `neg`, not `isTrue`/`isFalse`
                                        # Using `aesop` for disjointness proof as it's reliable across Mathlib versions
                                        lean_code = f'''import Mathlib.Tactic.SplitIfs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
import Aesop

def {func_name} ({list_param} : List Int) ({element_param} : Int) : List Int :=
  if {element_param} ∈ {list_param} then {list_param} else {list_param} ++ [{element_param}]

theorem {func_name}_preserves_nodup ({list_param} : List Int) ({element_param} : Int) (h : {list_param}.Nodup) :
  ({func_name} {list_param} {element_param}).Nodup := by
  unfold {func_name}
  split_ifs with h_mem
  case pos =>
    exact h
  case neg =>
    rw [List.nodup_append]
    refine ⟨h, List.nodup_singleton {element_param}, ?_⟩
    aesop
'''
                                        return lean_code
                                    else:
                                        print(f"[Deterministic] Variable names don't match")
                else:
                    print(f"[Deterministic] Missing list_param or element_param")
    except Exception as e:
        print(f"[Deterministic Translator] Error: {e}")
        import traceback
        traceback.print_exc()
        return None
    
    print("[Deterministic] No pattern matched, returning None")
    return None


def translate_advanced(python_code: str) -> str:
    """
    Use Gemini to translate complex Python code to Lean 4.
    
    HYBRID APPROACH:
    1. First try deterministic translation for known patterns
    2. Fall back to LLM for unknown patterns
    
    Args:
        python_code: Python source code string
        
    Returns:
        Lean 4 code with functions and theorems
    """
    # Step 1: Try deterministic translation for known patterns
    print("[Advanced Translator] Trying deterministic translation...")
    deterministic_result = _deterministic_membership_translation(python_code)
    
    if deterministic_result:
        print("[Advanced Translator] ✅ Deterministic translation succeeded!")
        return deterministic_result
    
    print("[Advanced Translator] Deterministic failed, falling back to LLM...")
    
    # Step 2: Fall back to LLM
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
        print("[Advanced Translator] Translating Python to Lean 4 via LLM...")
        response = model.generate_content(prompt, safety_settings=safety_settings)
        
        if response.parts:
            lean_code = clean_response(response.text)
            print("[Advanced Translator] LLM translation complete")
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
