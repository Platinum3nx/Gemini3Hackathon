import sys
import os
from unittest.mock import MagicMock, patch

# Add current directory to path
sys.path.append(os.getcwd())

from backend import repo_manager

# Mock git.Repo.clone_from to avoid actual network/disk usage
# Mock agents.triage_files to avoid API calls

import sys
import os
import shutil
from unittest.mock import MagicMock, patch

# Add current directory to path
sys.path.append(os.getcwd())

from backend import repo_manager

# Mock git.Repo.clone_from to avoid actual network/disk usage
# Mock agents.triage_files to avoid API calls

@patch('backend.repo_manager.git.Repo.clone_from')
@patch('backend.repo_manager.tempfile.mkdtemp')
def test_clone_repo(mock_mkdtemp, mock_clone):
    print("Testing repo_manager.clone_repo...")
    mock_mkdtemp.return_value = "/tmp/fake_repo"
    
    path = repo_manager.clone_repo("https://github.com/fake/repo")
    
    mock_clone.assert_called_with("https://github.com/fake/repo", "/tmp/fake_repo", depth=1)
    assert path == "/tmp/fake_repo"
    print("Clone verified.")

@patch('backend.repo_manager.os.walk')
@patch('backend.repo_manager.agents.triage_files')
def test_get_critical_files(mock_triage, mock_walk):
    print("Testing repo_manager.get_critical_files...")
    
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
    
    files = repo_manager.get_critical_files("/tmp/fake_repo")
    
    # Verify Triage called with correct files (filtered)
    args, _ = mock_triage.call_args
    print(f"Files sent to triage: {args[0]}")
    
    assert "auth.py" in args[0]
    assert "main.py" in args[0]
    assert "utils/helper.py" in args[0]
    assert ".git/config" not in args[0]
    
    assert files == ["auth.py", "main.py", "utils/helper.py"]
    print("Critical files logic verified.")

if __name__ == "__main__":
    test_clone_repo()
    test_get_critical_files()
    print("All repo logic tests passed!")
