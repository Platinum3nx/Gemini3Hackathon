import os
import shutil
import tempfile
import git
import subprocess
from typing import List
from . import agents
import pathspec

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

def load_argusignore(repo_path: str) -> pathspec.PathSpec:
    """
    Loads .argusignore from the repo root and returns a PathSpec object.
    Returns an empty PathSpec if the file doesn't exist.
    """
    ignore_path = os.path.join(repo_path, '.argusignore')
    if os.path.exists(ignore_path):
        try:
            with open(ignore_path, 'r') as f:
                return pathspec.PathSpec.from_lines('gitwildmatch', f)
        except Exception as e:
            print(f"Error loading .argusignore: {e}")
            
    return pathspec.PathSpec.from_lines('gitwildmatch', [])

def get_all_python_files(repo_path: str) -> List[str]:
    """
    Walks the directory and returns a list of .py files, ignoring standard ignored dirs AND .argusignore patterns.
    """
    py_files = []
    # Hardcoded critical ignores - these are always skipped for performance/safety
    ignore_dirs = {'.git', '__pycache__', 'venv', 'env', 'node_modules', 'tests', 'test', 'docs'}
    
    # Load user-defined ignores
    spec = load_argusignore(repo_path)
    
    for root, dirs, files in os.walk(repo_path):
        # Modify dirs in-place to skip ignored directories
        dirs[:] = [d for d in dirs if d not in ignore_dirs]
        
        for file in files:
            if file.endswith('.py'):
                full_path = os.path.join(root, file)
                # Store relative path for cleaner agent consumption
                rel_path = os.path.relpath(full_path, start=repo_path)
                
                # Check against .argusignore
                if not spec.match_file(rel_path):
                    py_files.append(rel_path)
                
    return py_files

def get_changed_files(repo_path: str) -> List[str]:
    """
    Identifies changed Python files between HEAD and HEAD^.
    Falls back to scanning all files if git diff fails (e.g., shallow clone or first commit).
    """
    print("Checking for changed files...")
    try:
        # Run git diff --name-only HEAD^ HEAD
        result = subprocess.run(
            ["git", "diff", "--name-only", "HEAD^", "HEAD"],
            cwd=repo_path,
            capture_output=True,
            text=True,
            check=True
        )
        changed_files = result.stdout.strip().splitlines()
        
        # Filter for .py files that currently exist
        valid_files = []
        spec = load_argusignore(repo_path)
        
        for f in changed_files:
            if f.endswith('.py') and os.path.exists(os.path.join(repo_path, f)):
                # Check against .argusignore
                if not spec.match_file(f):
                    valid_files.append(f)
                
        print(f"Incremental scan identified {len(valid_files)} changed Python files.")
        return valid_files
        
    except subprocess.CalledProcessError:
        print("Incremental scan failed (likely shallow clone or first commit). Falling back to full scan.")
        return get_all_python_files(repo_path)
    except Exception as e:
        print(f"Error during incremental scan: {e}. Falling back to full scan.")
        return get_all_python_files(repo_path)

def get_critical_files(repo_path: str) -> List[str]:
    """
    Identifies the top 3 critical files in the repo using the Triage Agent.
    """
    print("Analyzing file structure...")
    file_list = get_all_python_files(repo_path)
    
    if not file_list:
        print("No Python files found in repository.")
        return []
        
    print(f"Found {len(file_list)} Python files. Sending to Agent for triage...")
    high_risk_files = agents.triage_files(file_list)
    
    print("Triage complete. High risk files:")
    for f in high_risk_files:
        print(f" - {f}")
        
    return high_risk_files
