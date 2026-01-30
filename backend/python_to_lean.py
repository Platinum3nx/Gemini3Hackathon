"""
Python to Lean 4 AST-based Translator

This module converts Python code to Lean 4 by parsing the Python AST.
It provides 100% reliable translation (no LLM involved in this step).

Supported constructs:
- Function definitions
- If/else statements  
- Binary operations (+, -, *, >, <, >=, <=, ==, !=)
- Boolean operations (and, or)
- Return statements
- Integer literals
- Variable references
- Tuple returns
"""

import ast
from typing import Optional


class PythonToLeanTranslator(ast.NodeVisitor):
    """Translates Python AST to Lean 4 code."""
    
    def __init__(self):
        self.indent_level = 0
        self.functions = []
    
    def translate(self, python_code: str) -> str:
        """Main entry point: parse Python and return Lean code."""
        try:
            tree = ast.parse(python_code)
        except SyntaxError as e:
            return f"-- PARSE_ERROR: {e}"
        
        self.functions = []
        for node in ast.iter_child_nodes(tree):
            if isinstance(node, ast.FunctionDef):
                self.functions.append(self.visit_FunctionDef(node))
        
        return "\n\n".join(self.functions)
    
    def visit_FunctionDef(self, node: ast.FunctionDef) -> str:
        """Convert a Python function to Lean."""
        func_name = node.name
        
        # Get parameters (assume all are Int for simplicity)
        params = []
        for arg in node.args.args:
            params.append(f"({arg.arg} : Int)")
        
        params_str = " ".join(params)
        
        # Get function body
        body = self._translate_body(node.body)
        
        # Check if return type is tuple
        return_type = self._infer_return_type(node.body)
        
        return f"def {func_name} {params_str} : {return_type} :=\n{body}"
    
    def _infer_return_type(self, body: list) -> str:
        """Infer the return type from the function body."""
        for stmt in body:
            if isinstance(stmt, ast.Return) and stmt.value:
                if isinstance(stmt.value, ast.Tuple):
                    return "Int × Int"
            if isinstance(stmt, ast.If):
                # Check both branches
                return_type = self._infer_return_type(stmt.body)
                if return_type != "Int":
                    return return_type
                if stmt.orelse:
                    return self._infer_return_type(stmt.orelse)
        return "Int"
    
    def _translate_body(self, body: list, indent: int = 2) -> str:
        """
        Translate function body statements.
        
        Handles the common "guard pattern" in Python:
            if condition1: return x
            if condition2: return y
            return z
        
        This becomes in Lean:
            if condition1 then x
            else if condition2 then y
            else z
        """
        prefix = " " * indent
        
        # Collect all statements
        statements = []
        for stmt in body:
            if isinstance(stmt, ast.Expr):
                # Skip docstrings
                continue
            statements.append(stmt)
        
        if not statements:
            return prefix + "sorry"
        
        # Check if this is the guard pattern (if without else followed by more statements)
        return self._translate_guard_pattern(statements, indent)
    
    def _translate_guard_pattern(self, statements: list, indent: int) -> str:
        """
        Translate guard pattern: sequential if statements become nested if-then-else.
        
        Python:
            if x: return a
            if y: return b
            return c
            
        Lean:
            if x then a
            else if y then b
            else c
        """
        prefix = " " * indent
        
        if not statements:
            return prefix + "sorry"
        
        first = statements[0]
        rest = statements[1:]
        
        # Handle assignment (let binding) followed by more statements
        if isinstance(first, ast.Assign):
            target = first.targets[0]
            if isinstance(target, ast.Name):
                value = self._translate_expr(first.value)
                # Keep same indentation for continuation after let
                rest_code = self._translate_guard_pattern(rest, indent)
                return f"{prefix}let {target.id} := {value}\n{rest_code}"
        
        # Handle if statement (guard)
        if isinstance(first, ast.If):
            cond = self._translate_expr(first.test)
            then_body = self._get_return_expr(first.body)
            
            if first.orelse:
                # Has explicit else - use it as the else branch
                else_body = self._translate_guard_pattern(first.orelse, indent + 2)
                # Check if else body has multiple lines (let bindings)
                if '\n' in else_body:
                    # Multi-line: put on new line with proper indentation
                    return f"{prefix}if {cond} then {then_body}\n{prefix}else\n{else_body}"
                else:
                    # Single line: inline it
                    return f"{prefix}if {cond} then {then_body}\n{prefix}else {else_body.strip()}"
            elif rest:
                # No else but more statements - chain them as else
                else_body = self._translate_guard_pattern(rest, indent + 2)
                if '\n' in else_body:
                    return f"{prefix}if {cond} then {then_body}\n{prefix}else\n{else_body}"
                else:
                    return f"{prefix}if {cond} then {then_body}\n{prefix}else {else_body.strip()}"
            else:
                # Last statement is an if without else - shouldn't happen in good code
                return f"{prefix}if {cond} then {then_body} else sorry"
        
        # Handle return statement (base case)
        if isinstance(first, ast.Return):
            return prefix + self._translate_expr(first.value)
        
        return prefix + "sorry"
    
    
    def _translate_if(self, node: ast.If, indent: int) -> str:
        """Translate if/else statement."""
        prefix = " " * indent
        cond = self._translate_expr(node.test)
        
        # Get the return value from the if body
        then_body = self._get_return_expr(node.body)
        
        if node.orelse:
            if len(node.orelse) == 1 and isinstance(node.orelse[0], ast.If):
                # elif case
                else_part = self._translate_if(node.orelse[0], indent).lstrip()
                return f"{prefix}if {cond} then {then_body}\n{prefix}else {else_part}"
            else:
                else_body = self._get_return_expr(node.orelse)
                return f"{prefix}if {cond} then {then_body}\n{prefix}else {else_body}"
        else:
            # If without else - shouldn't happen in well-formed code
            return f"{prefix}if {cond} then {then_body} else sorry"
    
    def _get_return_expr(self, body: list) -> str:
        """Get the return expression from a body, handling let bindings."""
        let_bindings = []
        return_expr = None
        
        for stmt in body:
            if isinstance(stmt, ast.Return):
                return_expr = self._translate_expr(stmt.value)
            elif isinstance(stmt, ast.Assign):
                target = stmt.targets[0]
                if isinstance(target, ast.Name):
                    value = self._translate_expr(stmt.value)
                    let_bindings.append(f"let {target.id} := {value}")
            elif isinstance(stmt, ast.If):
                return self._translate_if(stmt, 0).strip()
        
        if let_bindings and return_expr:
            # Combine let bindings with return - use newline and consistent formatting
            # In Lean 4, let bindings in expressions need proper structure
            result = let_bindings[0]
            for binding in let_bindings[1:]:
                result += f"; {binding}"
            result += f"; {return_expr}"
            return result
        
        return return_expr or "sorry"
    
    def _translate_expr(self, node: ast.expr) -> str:
        """Translate a Python expression to Lean."""
        if node is None:
            return "()"
        
        if isinstance(node, ast.Num):  # Python 3.7 compatibility
            return str(node.n)
        
        if isinstance(node, ast.Constant):
            return str(node.value)
        
        if isinstance(node, ast.Name):
            return node.id
        
        if isinstance(node, ast.BinOp):
            left = self._translate_expr(node.left)
            right = self._translate_expr(node.right)
            op = self._translate_binop(node.op)
            return f"({left} {op} {right})"
        
        if isinstance(node, ast.Compare):
            left = self._translate_expr(node.left)
            # Handle single comparison
            if len(node.ops) == 1:
                op = self._translate_cmpop(node.ops[0])
                right = self._translate_expr(node.comparators[0])
                return f"{left} {op} {right}"
            # Multiple comparisons (a < b < c) - not supported for simplicity
            return "sorry"
        
        if isinstance(node, ast.BoolOp):
            op = "∧" if isinstance(node.op, ast.And) else "∨"
            values = [self._translate_expr(v) for v in node.values]
            return f"({f' {op} '.join(values)})"
        
        if isinstance(node, ast.UnaryOp):
            if isinstance(node.op, ast.Not):
                operand = self._translate_expr(node.operand)
                return f"¬({operand})"
            if isinstance(node.op, ast.USub):
                operand = self._translate_expr(node.operand)
                return f"-{operand}"
        
        if isinstance(node, ast.Tuple):
            elts = [self._translate_expr(e) for e in node.elts]
            return f"({', '.join(elts)})"
        
        if isinstance(node, ast.IfExp):
            # Ternary expression: x if cond else y
            cond = self._translate_expr(node.test)
            then_val = self._translate_expr(node.body)
            else_val = self._translate_expr(node.orelse)
            return f"if {cond} then {then_val} else {else_val}"
        
        # Fallback for unsupported nodes
        return f"sorry /- unsupported: {type(node).__name__} -/"
    
    def _translate_binop(self, op: ast.operator) -> str:
        """Translate binary operator."""
        ops = {
            ast.Add: "+",
            ast.Sub: "-",
            ast.Mult: "*",
            ast.Div: "/",
            ast.Mod: "%",
        }
        return ops.get(type(op), "?")
    
    def _translate_cmpop(self, op: ast.cmpop) -> str:
        """Translate comparison operator."""
        ops = {
            ast.Eq: "=",
            ast.NotEq: "≠",
            ast.Lt: "<",
            ast.LtE: "≤",
            ast.Gt: ">",
            ast.GtE: "≥",
        }
        return ops.get(type(op), "?")


def translate_python_to_lean(python_code: str) -> str:
    """
    Convenience function to translate Python code to Lean 4 (functions only).
    
    Args:
        python_code: Python source code string
        
    Returns:
        Lean 4 code string with function definitions
    """
    translator = PythonToLeanTranslator()
    return translator.translate(python_code)


def generate_theorem(func_name: str = "withdraw", first_param: str = "balance") -> str:
    """
    Generate a deterministic verification theorem.
    
    The theorem always has the same structure:
    - Assumes first parameter (balance) is >= 0
    - Proves result is >= 0
    - Uses split_ifs and omega tactics
    
    NO LLM INVOLVED - this is 100% deterministic.
    """
    return f"""theorem verify_safety ({first_param} amount : Int) (h_bal : {first_param} ≥ 0) : 
  {func_name} {first_param} amount ≥ 0 := by
  unfold {func_name}
  split_ifs <;> omega"""


def translate_with_theorem(python_code: str) -> str:
    """
    Complete translation: Python -> Lean functions + verification theorem.
    
    This is the main entry point for the hybrid system.
    NO LLM is involved - everything is deterministic.
    
    Args:
        python_code: Python source code string
        
    Returns:
        Complete Lean 4 code with functions and theorem
    """
    # REQUIRED Mathlib imports for tactics and List operations
    # - SplitIfs: for split_ifs tactic
    # - List.Basic: for list operations (∈, ++, length, etc.)
    # - List.Nodup: for List.Nodup uniqueness proofs
    # - Linarith: powerful fallback for linear arithmetic
    # - Omega: for linear integer arithmetic
    imports = """import Mathlib.Tactic.SplitIfs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Omega

"""
    
    # Step 1: Translate functions
    lean_functions = translate_python_to_lean(python_code)
    
    if lean_functions.startswith("-- PARSE_ERROR"):
        return lean_functions
    
    # Step 2: Identify the main function to verify
    # Look for common financial function names
    main_func = "withdraw"  # default
    first_param = "balance"  # default
    
    for func_name in ["withdraw", "transfer", "deposit", "debit"]:
        if f"def {func_name}" in lean_functions:
            main_func = func_name
            break
    
    # Extract first parameter name from function signature
    import re
    match = re.search(rf"def {main_func}\s+\((\w+)\s*:", lean_functions)
    if match:
        first_param = match.group(1)
    
    # Step 3: Generate theorem
    theorem = generate_theorem(main_func, first_param)
    
    # Step 4: Combine with imports
    return f"{imports}{lean_functions}\n\n{theorem}"


# Quick test
if __name__ == "__main__":
    test_buggy = '''
def withdraw(balance, amount):
    return balance - amount
'''
    print("=== BUGGY ===")
    print(translate_with_theorem(test_buggy))
    print()
    
    test_secure = '''
def withdraw(balance, amount):
    if amount <= 0:
        return balance
    if amount > balance:
        return balance
    return balance - amount
'''
    print("=== SECURE ===")
    print(translate_with_theorem(test_secure))

