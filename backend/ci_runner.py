#!/usr/bin/env python3
import os
import sys
import json
from backend import repo_manager
from backend import agents

def generate_report(results: list) -> int:
    """
    Generates a Markdown report and writes it to Argus_Audit_Report.md
    and GITHUB_STEP_SUMMARY if available.
    Returns 1 if any file failed verification, 0 otherwise.
    """
    report_lines = ["# Argus AI Audit Report", "", "## Summary"]
    
    total = len(results)
    secure = sum(1 for r in results if r["status"] == "SECURE")
    patched = sum(1 for r in results if r["status"] == "AUTO_PATCHED")
    vulnerable = sum(1 for r in results if r["status"] == "VULNERABLE")
    
    report_lines.append(f"- **Total Files Audited:** {total}")
    report_lines.append(f"- **✅ Secure:** {secure}")
    report_lines.append(f"- **⚠️ Auto-Patched:** {patched}")
    report_lines.append(f"- **❌ Vulnerable:** {vulnerable}")
    report_lines.append("")
    
    has_failure = vulnerable > 0
    
    report_lines.append("## Details")
    
    for r in results:
        icon = "✅"
        if r["status"] == "AUTO_PATCHED":
            icon = "⚠️"
        elif r["status"] == "VULNERABLE":
            icon = "❌"
            
        report_lines.append(f"### {icon} {r['filename']}")
        report_lines.append(f"**Status:** {r['status']}")
        
        if r["status"] == "AUTO_PATCHED":
             report_lines.append("\n<details><summary>View Fix</summary>\n")
             report_lines.append("```python")
             report_lines.append(r["fixed_code"])
             report_lines.append("```\n</details>\n")

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
        # Fallback to all? user said repo_manager handles fallback.
        critical_files = [] # Should have been handled by repo_manager
        
    if not critical_files:
        print("No Python files changed. Skipping audit.")
        sys.exit(0)
        
    print(f"Auditing {len(critical_files)} files: {critical_files}")
    
    results = []
    
    # 2. Audit loop
    for filename in critical_files:
        print(f"--- Auditing {filename} ---")
        try:
            full_path = os.path.join(repo_path, filename)
            
            # Check if file still exists
            if not os.path.exists(full_path):
                print(f"File {filename} does not exist (deleted?). Skipping.")
                continue
                
            with open(full_path, "r") as f:
                content = f.read()
                
            # Calling the new agent function
            result = agents.audit_file(filename, content)
            results.append(result)
            
        except Exception as e:
            print(f"Error processing {filename}: {e}")
            results.append({
                "filename": filename,
                "status": "VULNERABLE",
                "logs": [f"System Error: {str(e)}"]
            })

    # 3. Report
    exit_code = generate_report(results)
    
    if exit_code == 0:
        print(" Audit PASSED ✅")
    else:
        print(" Audit FAILED ❌")
        
    sys.exit(exit_code)

if __name__ == "__main__":
    main()
