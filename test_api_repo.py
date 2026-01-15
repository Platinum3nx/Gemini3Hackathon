from fastapi.testclient import TestClient
from unittest.mock import patch, MagicMock
from backend.main import app

client = TestClient(app)

# Mock repo_manager.scan_repo to avoid Git operations
# Mock agents.call_gemini to avoid API usage
# Mock lean_driver.run_verification to avoid Lean usage

@patch('backend.main.repo_manager.scan_repo')
@patch('backend.main.agents.call_gemini')
@patch('backend.main.lean_driver.run_verification')
def test_audit_repo_endpoint(mock_verify, mock_gemini, mock_scan):
    print("Testing POST /audit_repo...")
    
    # 1. Setup Mocks
    # repo_manager returns 2 files
    mock_scan.return_value = [
        {"path": "main.py", "content": "def main(): pass"},
        {"path": "auth.py", "content": "def login(): pass"}
    ]
    
    # gemini returns "translated_code"
    mock_gemini.return_value = "theorem test : true := by trivial"
    
    # lean_driver returns verified=True
    mock_verify.return_value = {"verified": True, "error_message": ""}
    
    # 2. Make Request
    response = client.post("/audit_repo", json={"repo_url": "https://github.com/fake/repo"})
    
    # 3. Assertions
    assert response.status_code == 200
    data = response.json()
    
    print(f"Status: {data['status']}")
    print(f"Number of results: {len(data['results'])}")
    
    assert data["status"] == "complete"
    assert len(data["results"]) == 2
    
    # Check Result 1
    r1 = data["results"][0]
    assert r1["filename"] == "main.py"
    assert r1["status"] == "verified"
    print("Result 1: Verified")
    
    # Check Result 2
    r2 = data["results"][1]
    assert r2["filename"] == "auth.py"
    assert r2["status"] == "verified"
    print("Result 2: Verified")
    
    print("Test Passed!")

if __name__ == "__main__":
    test_audit_repo_endpoint()
