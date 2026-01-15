from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel
from typing import List, Dict, Any
from . import agents
from . import lean_driver
from . import repo_manager
import logging

app = FastAPI()

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

class VerificationRequest(BaseModel):
    python_code: str

class RepoRequest(BaseModel):
    repo_url: str

def process_single_file(code: str, filename: str = "snippet") -> Dict[str, Any]:
    """
    Reusable logic for translating, verifying, and fixing a single Python file.
    """
    original_code = code
    current_code = original_code
    
    # Step 1: Initial Translation
    print(f"[{filename}] Step 1: Translating Python to Lean...")
    lean_code = agents.call_gemini(agents.TRANSLATOR_PROMPT, current_code)
    
    # Step 2: Initial Verification
    print(f"[{filename}] Step 2: Verifying Lean code...")
    result = lean_driver.run_verification(lean_code)
    
    logs = [f"Initial verification result: {result['verified']}"]
    proof = lean_code
    
    retries = 0
    max_retries = 3
    
    # Step 3: Self-Healing Loop
    while not result["verified"] and retries < max_retries:
        retries += 1
        print(f"[{filename}] Verification failed. Attempt {retries}/{max_retries}. Fixing...")
        logs.append(f"Attempt {retries}: Verification failed. Error: {result['error_message'][:100]}...")
        
        # Logs to stdout
        print(f"[{filename}] Error: {result['error_message']}")
        
        # Fix
        print(f"[{filename}] Calling Fixer Agent...")
        fix_input = f"Original Python Code:\n{current_code}\n\nLean Error Message:\n{result['error_message']}"
        current_code = agents.call_gemini(agents.FIXER_PROMPT, fix_input)
        
        # Re-translate (Critical Step)
        print(f"[{filename}] Re-translating fixed code to Lean...")
        lean_code = agents.call_gemini(agents.TRANSLATOR_PROMPT, current_code)
        proof = lean_code
        
        # Re-verify
        print(f"[{filename}] Re-verifying...")
        result = lean_driver.run_verification(lean_code)
        logs.append(f"Attempt {retries} result: {result['verified']}")
        
    status = "verified" if result["verified"] else "failed"
    print(f"[{filename}] Final status: {status}")
    
    return {
        "status": status,
        "original_code": original_code,
        "fixed_code": current_code,
        "proof": proof,
        "logs": logs,
        "filename": filename
    }

@app.post("/audit")
def audit_code(request: VerificationRequest):
    print("Received single file audit request")
    # Wrap the new function to maintain backward compatibility
    return process_single_file(request.python_code)

@app.post("/audit_repo")
def audit_repo(request: RepoRequest):
    print(f"Received repo audit request: {request.repo_url}")
    
    # Step 1: Scan Repo
    try:
        high_risk_files = repo_manager.scan_repo(request.repo_url)
    except Exception as e:
        print(f"Repo scan failed: {e}")
        return {"status": "error", "message": str(e), "results": []}
    
    results = []
    
    # Step 2 & 3: Process each high-risk file
    for file_data in high_risk_files:
        print(f"Processing critical file: {file_data['path']}")
        file_result = process_single_file(file_data['content'], filename=file_data['path'])
        results.append(file_result)
        
    return {
        "status": "complete",
        "results": results
    }
