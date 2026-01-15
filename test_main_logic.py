import sys
import os
from unittest.mock import MagicMock, patch

# Add current directory to path
sys.path.append(os.getcwd())

from backend import main

# Mock dependencies
with patch('backend.agents.call_gemini') as mock_call_gemini, \
     patch('backend.lean_driver.run_verification') as mock_run_verification:
     
    print("Testing /audit endpoint logic...")
    
    # Scenario 1: Initial Success
    print("\n--- Scenario 1: Initial Success ---")
    mock_call_gemini.return_value = "theorem test : true := by simp"
    mock_run_verification.return_value = {"verified": True, "error_message": ""}
    
    req = main.VerificationRequest(python_code="def foo(): return 1")
    response = main.audit_code(req)
    
    print(f"Status: {response['status']}")
    assert response['status'] == "verified"
    assert mock_call_gemini.call_count == 1
    assert mock_run_verification.call_count == 1
    
    # Reset mocks
    mock_call_gemini.reset_mock()
    mock_run_verification.reset_mock()
    
    # Scenario 2: Fail then Fix
    print("\n--- Scenario 2: Fail then Fix ---")
    # 1. Translate (Initial) -> Lean1
    # 2. Fix -> Python2
    # 3. Translate -> Lean2
    mock_call_gemini.side_effect = ["Lean1", "Python2", "Lean2"]
    
    # 1. Verify (Initial) -> False
    # 2. Verify (After Fix) -> True
    mock_run_verification.side_effect = [
        {"verified": False, "error_message": "Error1"},
        {"verified": True, "error_message": ""}
    ]
    
    req = main.VerificationRequest(python_code="def foo(): return 1")
    response = main.audit_code(req)
    
    print(f"Status: {response['status']}")
    print(f"Fixed Code: {response['fixed_code']}")
    
    assert response['status'] == "verified"
    assert response['fixed_code'] == "Python2"
    # Calls: Translate1, Fix, Translate2
    assert mock_call_gemini.call_count == 3 
    # Calls: Verify1, Verify2
    assert mock_run_verification.call_count == 2
    
    print("\nTests Passed!")
