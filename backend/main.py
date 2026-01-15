from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel
import agents
import lean_driver
import logging

app = FastAPI()

app.add_middleware(
    CORSMiddleware,
    allow_origins=["http://localhost:3000"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

class VerificationRequest(BaseModel):
    python_code: str

@app.post("/audit")
def audit_code(request: VerificationRequest):
    print("Received audit request")
    original_code = request.python_code
    current_code = original_code
    
    # Step 1: Initial Translation
    print("Step 1: Translating Python to Lean...")
    lean_code = agents.call_gemini(agents.TRANSLATOR_PROMPT, current_code)
    
    # Step 2: Initial Verification
    print("Step 2: Verifying Lean code...")
    result = lean_driver.run_verification(lean_code)
    
    logs = [f"Initial verification result: {result['verified']}"]
    proof = lean_code
    
    retries = 0
    max_retries = 3
    
    # Step 3: Self-Healing Loop
    while not result["verified"] and retries < max_retries:
        retries += 1
        print(f"Verification failed. Attempt {retries}/{max_retries}. Fixing...")
        logs.append(f"Attempt {retries}: Verification failed. Error: {result['error_message'][:100]}...")
        
        # Logs to stdout
        print(f"Error: {result['error_message']}")
        
        # Fix
        print("Calling Fixer Agent...")
        fix_input = f"Original Python Code:\n{current_code}\n\nLean Error Message:\n{result['error_message']}"
        current_code = agents.call_gemini(agents.FIXER_PROMPT, fix_input)
        
        # Re-translate (Critical Step)
        print("Re-translating fixed code to Lean...")
        lean_code = agents.call_gemini(agents.TRANSLATOR_PROMPT, current_code)
        proof = lean_code
        
        # Re-verify
        print("Re-verifying...")
        result = lean_driver.run_verification(lean_code)
        logs.append(f"Attempt {retries} result: {result['verified']}")
        
    status = "verified" if result["verified"] else "failed"
    print(f"Final status: {status}")
    
    return {
        "status": status,
        "original_code": original_code,
        "fixed_code": current_code,
        "proof": proof,
        "logs": logs
    }
