from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import StreamingResponse
from pydantic import BaseModel
from typing import List, Dict, Any, AsyncGenerator
from . import agents
from . import lean_driver
from . import repo_manager
import logging
import json
import asyncio

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

async def process_single_file(code: str, filename: str = "snippet") -> AsyncGenerator[str, None]:
    """
    Async generator that yields JSON events for translating, verifying, and fixing a single Python file.
    """
    original_code = code
    current_code = original_code
    
    # Step 1: Initial Translation
    print(f"[{filename}] Step 1: Translating Python to Lean...")
    yield json.dumps({"type": "log", "status": "translating", "message": f"[{filename}] Translating Python to Lean 4..."}) + "\n"
    lean_code = agents.call_gemini(agents.TRANSLATOR_PROMPT, current_code)
    
    # Step 2: Initial Verification
    print(f"[{filename}] Step 2: Verifying Lean code...")
    yield json.dumps({"type": "log", "status": "verifying", "message": f"[{filename}] Running Formal Verification..."}) + "\n"
    result = lean_driver.run_verification(lean_code)
    
    initial_verified = result["verified"]
    
    logs = [f"Initial verification result: {initial_verified}"]
    proof = lean_code
    
    retries = 0
    max_retries = 3
    
    # Step 3: Self-Healing Loop
    while not result["verified"] and retries < max_retries:
        retries += 1
        print(f"[{filename}] Verification failed. Attempt {retries}/{max_retries}. Fixing...")
        yield json.dumps({"type": "log", "status": "failed", "message": f"[{filename}] Proof Failed. Engaging Self-Healing (Attempt {retries}/{max_retries})..."}) + "\n"
        logs.append(f"Attempt {retries}: Verification failed. Error: {result['error_message'][:100]}...")
        
        # Logs to stdout
        print(f"[{filename}] Error: {result['error_message']}")
        
        # Fix
        print(f"[{filename}] Calling Fixer Agent...")
        yield json.dumps({"type": "log", "status": "fixing", "message": f"[{filename}] Agent is patching the vulnerability..."}) + "\n"
        fix_input = f"Original Python Code:\n{current_code}\n\nLean Error Message:\n{result['error_message']}"
        current_code = agents.call_gemini(agents.FIXER_PROMPT, fix_input)
        
        # Re-translate (Critical Step)
        print(f"[{filename}] Re-translating fixed code to Lean...")
        yield json.dumps({"type": "log", "status": "translating", "message": f"[{filename}] Re-translating fixed code..."}) + "\n"
        lean_code = agents.call_gemini(agents.TRANSLATOR_PROMPT, current_code)
        proof = lean_code
        
        # Re-verify
        print(f"[{filename}] Re-verifying...")
        yield json.dumps({"type": "log", "status": "verifying", "message": f"[{filename}] Re-verifying fix..."}) + "\n"
        result = lean_driver.run_verification(lean_code)
        logs.append(f"Attempt {retries} result: {result['verified']}")
        
    final_verified = result["verified"]
    status = "verified" if final_verified else "failed"
    print(f"[{filename}] Final status: {status}")
    
    final_result_dict = {
        "status": status,
        "verified": initial_verified, # Was the original code verified?
        "fix_verified": final_verified, # Is the final code verified?
        "original_code": original_code,
        "fixed_code": current_code,
        "proof": proof,
        "logs": logs,
        "filename": filename
    }
    
    yield json.dumps({"type": "result", "filename": filename, "status": status, "proof": proof, "result": final_result_dict}) + "\n"

@app.post("/audit")
async def audit_code(request: VerificationRequest):
    print("Received single file audit request")
    return StreamingResponse(process_single_file(request.python_code), media_type="application/x-ndjson")

@app.post("/audit_repo")
async def audit_repo(request: RepoRequest):
    print(f"Received repo audit request: {request.repo_url}")
    
    async def repo_generator():
        yield json.dumps({"type": "log", "status": "scanning", "message": f"Cloning and scanning {request.repo_url}..."}) + "\n"
        
        repo_path = None
        import shutil
        import os

        # Step 1: Scan Repo
        try:
            repo_path = repo_manager.clone_repo(request.repo_url)
            critical_files = repo_manager.get_critical_files(repo_path)
            
            if not critical_files:
                 yield json.dumps({"type": "log", "status": "error", "message": "No critical Python files found."}) + "\n"
                 return

            results = []
            
            # Step 2 & 3: Process each high-risk file
            for filename in critical_files:
                print(f"Processing critical file: {filename}")
                yield json.dumps({"type": "file_start", "filename": filename}) + "\n"
                
                # Check if we should audit this file
                # process_single_file generator logic
                try:
                    full_path = os.path.join(repo_path, filename)
                    with open(full_path, 'r') as f:
                        code_content = f.read()

                    async for chunk in process_single_file(code_content, filename=filename):
                        data = json.loads(chunk)
                        if data.get("type") == "result":
                           results.append(data["result"])
                        yield chunk
                except Exception as e:
                     print(f"Error auditing {filename}: {e}")
                     yield json.dumps({"type": "log", "status": "error", "message": f"Error auditing {filename}: {str(e)}"}) + "\n"
                
                yield json.dumps({"type": "file_end", "filename": filename}) + "\n"
                
            # Overall completion event
            yield json.dumps({"type": "complete", "results": results}) + "\n"
            
        except Exception as e:
            print(f"Repo scan failed: {e}")
            yield json.dumps({"type": "log", "status": "error", "message": str(e)}) + "\n"
        finally:
            if repo_path and os.path.exists(repo_path):
                print(f"Cleaning up {repo_path}...")
                shutil.rmtree(repo_path)

    return StreamingResponse(repo_generator(), media_type="application/x-ndjson")
