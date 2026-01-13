import subprocess
import os
import uuid
import json
import re
from typing import Dict, Any, List

# Define the root of the Lean project
# Assuming this file is in <root>/backend/lean_driver.py
# and veritas_proofs is in <root>/veritas_proofs
BASE_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
VERITAS_PROJECT_PATH = os.path.join(BASE_DIR, "veritas_proofs")

def run_verification(lean_code: str) -> Dict[str, Any]:
    """
    Writes the code to a temporary .lean file inside the veritas_proofs project.
    Runs lean <file> via subprocess using `lake env`.
    Captures stdout and stderr.
    Returns a JSON object: {verified: bool, error_message: str, distinct_errors: list}.
    """
    
    # Generate a unique filename
    file_id = str(uuid.uuid4())
    filename = f"verify_{file_id}.lean"
    file_path = os.path.join(VERITAS_PROJECT_PATH, filename)

    try:
        # 1. Write the code to a temporary .lean file
        with open(file_path, "w") as f:
            f.write(lean_code)

        # 2. Run lean <file> via subprocess
        # We use `lake env lean <file>` to ensure Mathlib and other dependencies are in the path
        # subprocess.run requires the cwd to be the project root for `lake` to resolve configuration correctly
        cmd = ["lake", "env", "lean", filename]
        
        process = subprocess.run(
            cmd,
            cwd=VERITAS_PROJECT_PATH,
            capture_output=True,
            text=True
        )

        stdout = process.stdout
        stderr = process.stderr
        return_code = process.returncode

        # 3. Process results
        verified = (return_code == 0)
        
        # Combine stdout and stderr for the full error message if needed, 
        # but usually errors are in stderr or stdout depending on Lean version/configuration.
        # Lean 4 usually puts errors in stderr or stdout.
        full_output = (stdout + "\n" + stderr).strip()
        
        distinct_errors = []
        if not verified:
            # Basic parsing to extract distinct errors (one per line or block)
            # This is a simple heuristic; can be improved.
            # Filtering out empty lines and "info:" lines if desired, keeping it simple for now.
            distinct_errors = [line for line in full_output.splitlines() if line.strip() and "error:" in line]
            if not distinct_errors:
                 # Fallback if no explicit "error:" found but failed
                 distinct_errors = [line for line in full_output.splitlines() if line.strip()]

        return {
            "verified": verified,
            "error_message": full_output,
            "distinct_errors": distinct_errors
        }

    except Exception as e:
        return {
            "verified": False,
            "error_message": str(e),
            "distinct_errors": [str(e)]
        }
    finally:
        # Cleanup: remove the temporary file
        if os.path.exists(file_path):
            try:
                os.remove(file_path)
            except OSError:
                pass
