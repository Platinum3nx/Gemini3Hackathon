import sys
import os
from unittest.mock import MagicMock, patch

# Add current directory to path
sys.path.append(os.getcwd())

from backend import repo_manager

# Mock git.Repo.clone_from to avoid actual network/disk usage
# Mock agents.triage_files to avoid API calls

@patch('backend.repo_manager.git.Repo.clone_from')
@patch('backend.repo_manager.tempfile.mkdtemp')
@patch('backend.repo_manager.shutil.rmtree')
@patch('backend.repo_manager.os.walk')
@patch('backend.agents.triage_files')
def test_scan_repo(mock_triage, mock_walk, mock_rmtree, mock_mkdtemp, mock_clone):
    print("Testing repo_manager.scan_repo...")
    
    # 1. Setup Mocks
    mock_mkdtemp.return_value = "/tmp/fake_repo"
    
    # Mock os.walk to simulate a repo structure
    # Structure:
    # /tmp/fake_repo
    #   - main.py
    #   - auth.py
    #   - .git/
    #     - config
    mock_walk.return_value = [
        ("/tmp/fake_repo", [".git", "utils"], ["main.py", "auth.py", "README.md"]),
        ("/tmp/fake_repo/utils", [], ["helper.py"])
    ]
    
    # Mock Triage Agent
    mock_triage.return_value = ["auth.py", "main.py", "utils/helper.py"]
    
    # 2. Run Scan
    files = repo_manager.scan_repo("https://github.com/fake/repo")
    
    # 3. Assertions
    print(f"High risk files detected: {files}")
    
    # Verify cleanup (rmtree called)
    mock_rmtree.assert_called_with("/tmp/fake_repo")
    print("Cleanup verified: rmtree called.")
    
    # Verify clone called
    mock_clone.assert_called()
    print("Clone verified: git.Repo.clone_from called.")
    
    # Verify Triage called with correct files
    # Note: get_file_structure should have filtered .git/config and README.md (not .py)
    # Expected python files: main.py, auth.py, utils/helper.py
    # We can check what mock_triage was called with
    args, _ = mock_triage.call_args
    print(f"Files sent to triage: {args[0]}")
    
    assert "auth.py" in args[0]
    assert "main.py" in args[0]
    assert "utils/helper.py" in args[0]
    assert ".git/config" not in args[0]
    
    assert files == ["auth.py", "main.py", "utils/helper.py"]
    print("Test Passed!")

if __name__ == "__main__":
    test_scan_repo()
