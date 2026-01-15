from fastapi.testclient import TestClient
from unittest.mock import patch, MagicMock, AsyncMock
from backend.main import app
import json

client = TestClient(app)

# Use AsyncMock for async generator mocking

@patch('backend.main.repo_manager.scan_repo')
@patch('backend.main.agents.call_gemini')
@patch('backend.main.lean_driver.run_verification')
def test_streaming_endpoints(mock_verify, mock_gemini, mock_scan):
    print("Testing Streaming Endpoints...")
    
    # 1. Mock Data
    mock_scan.return_value = [{"path": "main.py", "content": "print('hello')"}]
    mock_gemini.return_value = "theorem test : true := by trivial"
    mock_verify.return_value = {"verified": True, "error_message": ""}
    
    # 2. Test /audit (Single File)
    print("\n[Testing POST /audit]...")
    response = client.post("/audit", json={"python_code": "print('test')"})
    assert response.status_code == 200
    
    # Check stream of events
    events = []
    for line in response.iter_lines():
        if line:
            events.append(json.loads(line))
            print(f"Received event: {line}")
            
    assert len(events) >= 3 # translating, verifying, success
    assert events[0]["type"] == "log"
    assert events[-1]["type"] == "result"
    print("PASS: /audit returns valid stream.")
    
    # 3. Test /audit_repo (Repo)
    print("\n[Testing POST /audit_repo]...")
    response = client.post("/audit_repo", json={"repo_url": "https://github.com/fake/repo"})
    assert response.status_code == 200
    
    repo_events = []
    for line in response.iter_lines():
        if line:
            repo_events.append(json.loads(line))
            print(f"Received event: {line}")
            
    # Expected flow: log (scanning) -> file_start -> [events] -> result -> file_end -> complete
    assert repo_events[0]["type"] == "log"
    
    file_start = next(e for e in repo_events if e.get("type") == "file_start")
    assert file_start["filename"] == "main.py"
    
    complete = repo_events[-1]
    assert complete["type"] == "complete"
    
    print("PASS: /audit_repo returns valid stream.")

if __name__ == "__main__":
    test_streaming_endpoints()
