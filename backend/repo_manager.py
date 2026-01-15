import os
import shutil
import tempfile
import git
from typing import List, Any, Generator
from contextlib import contextmanager
from . import agents

@contextmanager
def temporary_clone(repo_url: str) -> Generator[str, None, None]:
    """
    Context manager that clones a repo to a temp directory and ensures cleanup.
    """
    temp_dir = tempfile.mkdtemp()
    print(f"Cloning {repo_url} into {temp_dir}...")
    try:
        git.Repo.clone_from(repo_url, temp_dir, depth=1)
        yield temp_dir
    finally:
        print(f"Cleaning up {temp_dir}...")
        shutil.rmtree(temp_dir)

def get_file_structure(repo_path: str) -> List[str]:
    """
    Walks the directory and returns a list of .py files, ignoring standard ignored dirs.
    """
    py_files = []
    ignore_dirs = {'.git', '__pycache__', 'venv', 'env', 'node_modules', 'tests', 'test', 'docs'}
    
    for root, dirs, files in os.walk(repo_path):
        # Modify dirs in-place to skip ignored directories
        dirs[:] = [d for d in dirs if d not in ignore_dirs]
        
        for file in files:
            if file.endswith('.py'):
                full_path = os.path.join(root, file)
                # Store relative path for cleaner agent consumption
                rel_path = os.path.relpath(full_path, start=repo_path)
                py_files.append(rel_path)
                
    return py_files

def scan_repo(repo_url: str) -> List[dict]:
    """
    Orchestrates the repo scan: Clone -> List Files -> Triage.
    Returns the list of 3 high-risk files identified by Gemini.
    """
    with temporary_clone(repo_url) as repo_path:
        print("Analyzing file structure...")
        file_list = get_file_structure(repo_path)
        
        if not file_list:
            print("No Python files found in repository.")
            return []
            
        print(f"Found {len(file_list)} Python files. Sending to Agent for triage...")
        high_risk_files = agents.triage_files(file_list)
        
        print("Triage complete. High risk files:")
        results = []
        for f in high_risk_files:
            print(f" - {f}")
            # Read content before temp dir is deleted
            full_path = os.path.join(repo_path, f)
            try:
                with open(full_path, "r") as file_obj:
                    content = file_obj.read()
                    results.append({"path": f, "content": content})
            except Exception as e:
                print(f"Error reading {f}: {e}")
        
        return results
