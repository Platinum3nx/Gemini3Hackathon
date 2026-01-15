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
    yield json.dumps({"status": "translating", "message": f"[{filename}] Translating Python to Lean 4..."}) + "\n"
    lean_code = agents.call_gemini(agents.TRANSLATOR_PROMPT, current_code)
    
    # Step 2: Initial Verification
    print(f"[{filename}] Step 2: Verifying Lean code...")
    yield json.dumps({"status": "verifying", "message": f"[{filename}] Running Formal Verification..."}) + "\n"
    result = lean_driver.run_verification(lean_code)
    
    logs = [f"Initial verification result: {result['verified']}"]
    proof = lean_code
    
    retries = 0
    max_retries = 3
    
    # Step 3: Self-Healing Loop
    while not result["verified"] and retries < max_retries:
        retries += 1
        print(f"[{filename}] Verification failed. Attempt {retries}/{max_retries}. Fixing...")
        yield json.dumps({"status": "failed", "error": "VerificationFailed", "message": f"[{filename}] Proof Failed. Engaging Self-Healing (Attempt {retries}/{max_retries})..."}) + "\n"
        logs.append(f"Attempt {retries}: Verification failed. Error: {result['error_message'][:100]}...")
        
        # Logs to stdout
        print(f"[{filename}] Error: {result['error_message']}")
        
        # Fix
        print(f"[{filename}] Calling Fixer Agent...")
        yield json.dumps({"status": "fixing", "message": f"[{filename}] Agent is patching the vulnerability..."}) + "\n"
        fix_input = f"Original Python Code:\n{current_code}\n\nLean Error Message:\n{result['error_message']}"
        current_code = agents.call_gemini(agents.FIXER_PROMPT, fix_input)
        
        # Re-translate (Critical Step)
        print(f"[{filename}] Re-translating fixed code to Lean...")
        yield json.dumps({"status": "translating", "message": f"[{filename}] Re-translating fixed code..."}) + "\n"
        lean_code = agents.call_gemini(agents.TRANSLATOR_PROMPT, current_code)
        proof = lean_code
        
        # Re-verify
        print(f"[{filename}] Re-verifying...")
        yield json.dumps({"status": "verifying", "message": f"[{filename}] Re-verifying fix..."}) + "\n"
        result = lean_driver.run_verification(lean_code)
        logs.append(f"Attempt {retries} result: {result['verified']}")
        
    status = "verified" if result["verified"] else "failed"
    print(f"[{filename}] Final status: {status}")
    
    final_result_dict = {
        "status": status,
        "original_code": original_code,
        "fixed_code": current_code,
        "proof": proof,
        "logs": logs,
        "filename": filename
    }
    
    yield json.dumps({"status": "success", "result": final_result_dict}) + "\n"

@app.post("/audit")
async def audit_code(request: VerificationRequest):
    print("Received single file audit request")
    return StreamingResponse(process_single_file(request.python_code), media_type="application/x-ndjson")

@app.post("/audit_repo")
async def audit_repo(request: RepoRequest):
    print(f"Received repo audit request: {request.repo_url}")
    
    async def repo_generator():
        yield json.dumps({"status": "scanning", "message": f"Cloning and scanning {request.repo_url}..."}) + "\n"
        
        # Step 1: Scan Repo
        try:
            # Note: synchronous call here, but that's fine for now or could be offloaded
            high_risk_files = repo_manager.scan_repo(request.repo_url)
        except Exception as e:
            print(f"Repo scan failed: {e}")
            yield json.dumps({"status": "error", "message": str(e)}) + "\n"
            return
        
        results = []
        
        # Step 2 & 3: Process each high-risk file
        for file_data in high_risk_files:
            print(f"Processing critical file: {file_data['path']}")
            yield json.dumps({"status": "scanning", "message": f"Processing critical file: {file_data['path']}"}) + "\n"
            
            # Delegate to the single file generator
            async for chunk in process_single_file(file_data['content'], filename=file_data['path']):
                # We can intercept 'success' here if we want to build the final list
                # Or just pass thorough everything
                data = json.loads(chunk)
                if data.get("status") == "success":
                   results.append(data["result"])
                yield chunk
            
        # Overall completion event if needed, but the individual success events are key
        yield json.dumps({"status": "complete", "results": results}) + "\n"

    return StreamingResponse(repo_generator(), media_type="application/x-ndjson")
