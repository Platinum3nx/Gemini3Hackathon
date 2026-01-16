import os
import shutil
import tempfile
import git
from typing import List
from . import agents

def clone_repo(repo_url: str) -> str:
    """
    Clones a repo to a temporary directory and returns the path.
    Caller is responsible for cleaning up using shutil.rmtree().
    """
    temp_dir = tempfile.mkdtemp()
    print(f"Cloning {repo_url} into {temp_dir}...")
    try:
        git.Repo.clone_from(repo_url, temp_dir, depth=1)
        return temp_dir
    except Exception as e:
        # If clone fails, clean up immediately and re-raise
        shutil.rmtree(temp_dir)
        raise e

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

def get_critical_files(repo_path: str) -> List[str]:
    """
    Identifies the top 3 critical files in the repo using the Triage Agent.
    """
    print("Analyzing file structure...")
    file_list = get_file_structure(repo_path)
    
    if not file_list:
        print("No Python files found in repository.")
        return []
        
    print(f"Found {len(file_list)} Python files. Sending to Agent for triage...")
    high_risk_files = agents.triage_files(file_list)
    
    print("Triage complete. High risk files:")
    for f in high_risk_files:
        print(f" - {f}")
        
    return high_risk_files
