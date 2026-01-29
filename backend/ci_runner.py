#!/usr/bin/env python3
"""
Argus CI Runner - Main orchestrator for the audit workflow.

Integrates the Neuro-Symbolic Repair Loop:
1. Audit files using deterministic translation + Lean verification
2. If VULNERABLE, attempt AI-powered repair using Gemini
3. Verify the fix to ensure it actually passes
4. Generate comprehensive report
"""

import os
import sys
import json
from backend import repo_manager
from backend import agents
from backend.ai_repair import generate_fix


def attempt_repair(filename: str, original_code: str, lean_error: str, repo_path: str) -> dict:
    """
    Attempt to repair vulnerable code using Gemini.
    
    Args:
        filename: Original filename
        original_code: The vulnerable Python code
        lean_error: The Lean error message explaining why verification failed
        repo_path: Path to the repository
        
    Returns:
        Dictionary with repair results
    """
    print(f"[{filename}] Attempting AI-powered repair...")
    
    try:
        # Generate fix using Gemini
        fixed_code = generate_fix(original_code, lean_error)
        
        if not fixed_code or len(fixed_code.strip()) < 10:
            print(f"[{filename}] AI returned empty or invalid fix")
            return {
                "attempted": True,
                "success": False,
                "reason": "AI returned empty or invalid code",
                "fixed_code": None,
                "fixed_filename": None
            }
        
        # Save the fixed code to a new file
        base_name = os.path.splitext(filename)[0]
        fixed_filename = f"{base_name}_fixed.py"
        fixed_path = os.path.join(repo_path, fixed_filename)
        
        with open(fixed_path, "w") as f:
            f.write(fixed_code)
        print(f"[{filename}] Fixed code saved to {fixed_filename}")
        
        # Verify the fix
        print(f"[{filename}] Verifying the AI-generated fix...")
        fix_result = agents.audit_file(fixed_filename, fixed_code)
        
        if fix_result["verified"]:
            print(f"[{filename}] ✅ AI fix PASSED verification!")
            return {
                "attempted": True,
                "success": True,
                "reason": "AI-generated fix passed formal verification",
                "fixed_code": fixed_code,
                "fixed_filename": fixed_filename,
                "fixed_proof": fix_result.get("proof")
            }
        else:
            print(f"[{filename}] ❌ AI fix FAILED verification")
            return {
                "attempted": True,
                "success": False,
                "reason": "AI-generated fix failed formal verification",
                "fixed_code": fixed_code,
                "fixed_filename": fixed_filename,
                "fixed_proof": fix_result.get("proof")
            }
            
    except Exception as e:
        print(f"[{filename}] Repair error: {e}")
        return {
            "attempted": True,
            "success": False,
            "reason": f"Repair error: {str(e)}",
            "fixed_code": None,
            "fixed_filename": None
        }


def generate_report(results: list) -> int:
    """
    Generates a Markdown report and writes it to Argus_Audit_Report.md
    and GITHUB_STEP_SUMMARY if available.
    Returns 1 if any file failed verification (and repair), 0 otherwise.
    """
    report_lines = ["# Argus AI Audit Report", "", "## Summary"]
    
    total = len(results)
    secure = sum(1 for r in results if r["status"] == "SECURE")
    patched = sum(1 for r in results if r["status"] == "AUTO_PATCHED")
    vulnerable = sum(1 for r in results if r["status"] == "VULNERABLE")
    
    report_lines.append(f"- **Total Files Audited:** {total}")
    report_lines.append(f"- **✅ Secure:** {secure}")
    report_lines.append(f"- **🔧 Auto-Patched:** {patched}")
    report_lines.append(f"- **❌ Vulnerable:** {vulnerable}")
    report_lines.append("")
    
    # Only fail if there are truly unfixed vulnerabilities
    has_failure = vulnerable > 0
    
    report_lines.append("## Details")
    
    for r in results:
        icon = "✅"
        if r["status"] == "AUTO_PATCHED":
            icon = "🔧"
        elif r["status"] == "VULNERABLE":
            icon = "❌"
            
        report_lines.append(f"### {icon} {r['filename']}")
        report_lines.append(f"**Status:** {r['status']}")
        
        # Show repair attempt info
        if r.get("repair_attempt"):
            repair = r["repair_attempt"]
            if repair.get("attempted"):
                if repair.get("success"):
                    report_lines.append(f"\n**🔧 Repair Attempt:** SUCCESS")
                    report_lines.append(f"- Fixed file: `{repair.get('fixed_filename')}`")
                else:
                    report_lines.append(f"\n**🔧 Repair Attempt:** FAILED")
                    report_lines.append(f"- Reason: {repair.get('reason')}")
        
        # Show fixed code for auto-patched files
        if r["status"] == "AUTO_PATCHED" and r.get("fixed_code"):
            report_lines.append("\n<details><summary>View Fix</summary>\n")
            report_lines.append("```python")
            report_lines.append(r["fixed_code"])
            report_lines.append("```\n</details>\n")

        # Show the formal proof
        if r.get("proof"):
            report_lines.append("\n<details><summary>View Formal Proof (Lean 4)</summary>\n")
            report_lines.append("```lean")
            report_lines.append(r["proof"])
            report_lines.append("```\n</details>\n")
             
        report_lines.append("---")

    report_content = "\n".join(report_lines)
    
    # Write to local file
    try:
        with open("Argus_Audit_Report.md", "w") as f:
            f.write(report_content)
        print("Report written to Argus_Audit_Report.md")
    except Exception as e:
        print(f"Error writing report file: {e}")

    # Write to GitHub Step Summary
    step_summary_path = os.environ.get("GITHUB_STEP_SUMMARY")
    if step_summary_path:
        try:
            with open(step_summary_path, "a") as f:
                f.write(report_content)
            print("Report appended to GITHUB_STEP_SUMMARY")
        except Exception as e:
            print(f"Error writing to GITHUB_STEP_SUMMARY: {e}")
            
    return 1 if has_failure else 0


def main():
    repo_path = os.environ.get("REPO_PATH", ".")
    print(f"Scanning repository at: {repo_path}")
    
    # 1. Get changed files (Smart Scan)
    try:
        critical_files = repo_manager.get_changed_files(repo_path)
    except Exception as e:
        print(f"Error getting changed files: {e}")
        critical_files = []
        
    if not critical_files:
        print("No Python files changed. Skipping audit.")
        sys.exit(0)
        
    print(f"Auditing {len(critical_files)} files: {critical_files}")
    
    results = []
    
    # 2. Audit loop with repair
    for filename in critical_files:
        print(f"\n{'='*50}")
        print(f"--- Auditing {filename} ---")
        print(f"{'='*50}")
        
        try:
            full_path = os.path.join(repo_path, filename)
            
            # Check if file still exists
            if not os.path.exists(full_path):
                print(f"File {filename} does not exist (deleted?). Skipping.")
                continue
                
            with open(full_path, "r") as f:
                content = f.read()
                
            # Initial audit
            result = agents.audit_file(filename, content)
            
            # If VULNERABLE, attempt repair
            if result["status"] == "VULNERABLE":
                print(f"\n[{filename}] ❌ VULNERABLE - Initiating repair loop...")
                
                # Get the Lean error message for the AI
                lean_error = result.get("proof", "Verification failed")
                
                # Attempt AI-powered repair
                repair_result = attempt_repair(
                    filename=filename,
                    original_code=content,
                    lean_error=lean_error,
                    repo_path=repo_path
                )
                
                result["repair_attempt"] = repair_result
                
                # If repair succeeded, update status to AUTO_PATCHED
                if repair_result.get("success"):
                    result["status"] = "AUTO_PATCHED"
                    result["fixed_code"] = repair_result.get("fixed_code")
                    result["fixed_filename"] = repair_result.get("fixed_filename")
                    print(f"[{filename}] Status updated to AUTO_PATCHED")
            
            results.append(result)
            
        except Exception as e:
            print(f"Error processing {filename}: {e}")
            results.append({
                "filename": filename,
                "status": "VULNERABLE",
                "logs": [f"System Error: {str(e)}"],
                "repair_attempt": {"attempted": False, "reason": str(e)}
            })

    # 3. Report
    print(f"\n{'='*50}")
    print("Generating report...")
    print(f"{'='*50}")
    
    exit_code = generate_report(results)
    
    if exit_code == 0:
        print("\n✅ Audit PASSED")
    else:
        print("\n❌ Audit FAILED - Some vulnerabilities could not be fixed")
        
    sys.exit(exit_code)


if __name__ == "__main__":
    main()
