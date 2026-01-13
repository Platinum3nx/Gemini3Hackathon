import sys
import os
import json

# Add current directory to path to find backend
sys.path.append(os.getcwd())

try:
    from backend.lean_driver import run_verification
except ImportError:
    # Try assuming we are in root and backend is a package
    from backend.lean_driver import run_verification

def test_bridge():
    print("Running Hello World test for Lean Bridge...")
    
    # Lean code that specifically imports Mathlib to test the constraint
    lean_code = """
import Mathlib.Data.Nat.Basic

example : 1 + 1 = 2 := by
  rfl
"""
    
    # If Mathlib isn't ready, this might fail or timeout, 
    # but we will try a simpler one first if we suspect timing issues,
    # however the requirement is to prove import Mathlib works.
    
    print(f"Lean Code:\n{lean_code}")
    
    result = run_verification(lean_code)
    
    print(json.dumps(result, indent=2))
    
    if result.get("verified"):
        print("✅ Verification SUCCESS")
    else:
        print("❌ Verification FAILED")

if __name__ == "__main__":
    test_bridge()
