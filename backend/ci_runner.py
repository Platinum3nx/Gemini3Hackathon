#!/usr/bin/env python3
import asyncio
import os
import sys
import json
import shutil
from backend import repo_manager
from backend.main import process_single_file  # Import the logic, ignore app instantiation

async def main():
    repo_url = os.environ.get("REPO_URL")
    repo_path_env = os.environ.get("REPO_PATH")
    commit_sha = os.environ.get("COMMIT_SHA", "HEAD")
    
    repo_path = None
    should_cleanup = False # Don't delete user's code if using REPO_PATH

    print(f"Starting Argus Headless Audit (Commit: {commit_sha})...", file=sys.stderr)
    
    all_results = []
    has_failure = False

    try:
        # 1. Determine Source (Clone vs Local)
        if repo_path_env:
            print(f"Using local repository path: {repo_path_env}", file=sys.stderr)
            repo_path = repo_path_env
            if not os.path.exists(repo_path):
                 print(f"Error: REPO_PATH {repo_path} does not exist.", file=sys.stderr)
                 sys.exit(1)
            # If repo_url isn't set, use the path as the "url" for reporting
            if not repo_url:
                repo_url = repo_path_env
        elif repo_url:
            print(f"Cloning repository from {repo_url}...", file=sys.stderr)
            repo_path = repo_manager.clone_repo(repo_url)
            should_cleanup = True
        else:
            print(json.dumps({"error": "Neither REPO_URL nor REPO_PATH environment variables are set."}))
            sys.exit(1)
        
        # 2. Triage
        print("Identifying critical files...", file=sys.stderr)
        critical_files = repo_manager.get_critical_files(repo_path)
        
        if not critical_files:
            print("No critical files found to audit.", file=sys.stderr)
            print(json.dumps({"status": "skipped", "message": "No Python files found."}))
            sys.exit(0)
            
        print(f"Auditing {len(critical_files)} files: {critical_files}", file=sys.stderr)
        
        # 3. Audit Loop
        for filename in critical_files:
            print(f"Auditing {filename}...", file=sys.stderr)
            full_path = os.path.join(repo_path, filename)
            
            try:
                with open(full_path, 'r') as f:
                    content = f.read()
                
                # Consume the streaming generator to find the result
                final_result = None
                async for chunk in process_single_file(content, filename=filename):
                    data = json.loads(chunk)
                    if data.get("type") == "result":
                        final_result = data.get("result")
                
                if final_result:
                    all_results.append(final_result)
                    if final_result["status"] != "verified":
                        # We also count 'patched' (where verification failed) as a failure 
                        # for strict CI, or we can allow it. User said "If ANY file fails verification".
                        # Usually "verified" means proven. "patched" might be partial success.
                        # Let's be strict: if status != "verified", it's a failure (exit 1).
                        has_failure = True
                else:
                    # No result returned?
                    print(f"Warning: No result returned for {filename}", file=sys.stderr)
                    has_failure = True
                    
            except Exception as e:
                print(f"Error processing {filename}: {e}", file=sys.stderr)
                has_failure = True
                all_results.append({
                    "filename": filename,
                    "status": "error",
                    "error": str(e)
                })

    except Exception as e:
        print(f"Critical System Error: {e}", file=sys.stderr)
        sys.exit(1)
        
    finally:
        if should_cleanup and repo_path and os.path.exists(repo_path):
            print("Cleaning up workspace...", file=sys.stderr)
            shutil.rmtree(repo_path)
            
    # 4. Output Report
    report = {
        "repo_url": repo_url,
        "commit_sha": commit_sha,
        "results": all_results,
        "summary": "failed" if has_failure else "passed"
    }
    
    print(json.dumps(report, indent=2))
    
    # 5. Exit Code
    if has_failure:
        print("Audit FAILED. Blocking merge.", file=sys.stderr)
        sys.exit(1)
    else:
        print("Audit PASSED. Ready to merge.", file=sys.stderr)
        sys.exit(0)

if __name__ == "__main__":
    asyncio.run(main())
