#!/usr/bin/env python3
"""
Argus CI Runner - Main orchestrator for the audit workflow.

Integrates the Neuro-Symbolic Repair Loop:
1. Audit files using deterministic translation + Lean verification
2. If VULNERABLE, attempt AI-powered repair using Gemini
3. Verify the fix to ensure it actually passes
4. Generate comprehensive report
5. Create auto-remediation PR with verified fixes
"""

import os
import sys
import json
from backend import repo_manager
from backend import agents
from backend.ai_repair import generate_fix
from backend.github_service import GitHubService
from backend.secrets_scanner import scan_repo, format_findings_for_report
from backend.sarif_generator import generate_sarif


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


def generate_report(results: list, secrets_findings: list = None) -> int:
    """
    Generates a Markdown report and writes it to Argus_Audit_Report.md
    and GITHUB_STEP_SUMMARY if available.
    Returns 1 if any file failed verification (and repair) or secrets found, 0 otherwise.
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
    
    # Only fail if there are truly unfixed vulnerabilities or HIGH severity secrets
    high_secrets = [f for f in (secrets_findings or []) if f.severity == "HIGH"]
    has_failure = vulnerable > 0 or len(high_secrets) > 0
    
    # Add secrets summary if any found
    if secrets_findings:
        report_lines.append(f"- **🔐 Secrets Detected:** {len(secrets_findings)}")
    
    report_lines.append("")
    
    # Add secrets section first if any found
    if secrets_findings:
        report_lines.append(format_findings_for_report(secrets_findings))
    
    report_lines.append("## Code Verification Details")
    
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
        
        # Show suggested fix for failed repairs (for human review)
        if r["status"] == "VULNERABLE" and r.get("suggested_fix"):
            report_lines.append("\n**⚠️ Suggested Fix (Unverified):**")
            report_lines.append("*This fix was generated by AI but could not be formally verified. Manual review recommended.*")
            report_lines.append("\n<details><summary>View Suggested Fix</summary>\n")
            report_lines.append("```python")
            report_lines.append(r["suggested_fix"])
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


def create_remediation_pr(all_fixed_content: dict, all_proofs: dict) -> str:
    """
    Create an auto-remediation PR with all verified fixes.
    
    Args:
        all_fixed_content: Dict mapping filenames to fixed code
        all_proofs: Dict mapping filenames to Lean proofs
        
    Returns:
        URL of the created PR, or None if failed
    """
    # Get GitHub environment variables
    github_token = os.getenv("GITHUB_TOKEN")
    repo_name = os.getenv("GITHUB_REPOSITORY")
    branch_name = os.getenv("GITHUB_REF_NAME")
    
    if not github_token:
        print("[PR Creation] GITHUB_TOKEN not set, skipping PR creation")
        return None
    
    if not repo_name:
        print("[PR Creation] GITHUB_REPOSITORY not set, skipping PR creation")
        return None
    
    if not branch_name:
        print("[PR Creation] GITHUB_REF_NAME not set, using 'main' as default")
        branch_name = "main"
    
    try:
        print(f"\n{'='*50}")
        print("Creating Auto-Remediation Pull Request...")
        print(f"{'='*50}")
        print(f"  Repository: {repo_name}")
        print(f"  Base branch: {branch_name}")
        print(f"  Files to fix: {list(all_fixed_content.keys())}")
        
        github_service = GitHubService(token=github_token)
        pr_url = github_service.create_fix_pr(
            repo_name=repo_name,
            original_branch=branch_name,
            fixes=all_fixed_content,
            proofs=all_proofs
        )
        
        return pr_url
        
    except Exception as e:
        print(f"[PR Creation] Error: {e}")
        return None


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
    
    # 1b. Run secrets scan on entire repo
    print(f"\n{'='*50}")
    print("Running Secrets Scan...")
    print(f"{'='*50}")
    secrets_findings = scan_repo(repo_path)
    
    if secrets_findings:
        print(f"⚠️  Found {len(secrets_findings)} potential secret(s)!")
    else:
        print("✅ No secrets detected")
    
    results = []
    
    # Data collection for PR creation
    all_fixed_content = {}
    all_proofs = {}
    
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
                    
                    # Capture fix for PR creation
                    # Store the fixed content using the ORIGINAL filename (so PR updates the original file)
                    all_fixed_content[filename] = repair_result.get("fixed_code")
                    all_proofs[filename] = repair_result.get("fixed_proof", "Proof verified successfully")
                else:
                    # Even if repair failed verification, capture the suggestion
                    # for human review (graceful degradation)
                    if repair_result.get("fixed_code"):
                        result["suggested_fix"] = repair_result.get("fixed_code")
                        # Note: We intentionally don't add to all_fixed_content since it's not verified
                        # The PR will only contain verified fixes
            
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
    
    exit_code = generate_report(results, secrets_findings)
    
    # 3b. Generate SARIF output
    print("Generating SARIF output...")
    try:
        sarif_data = generate_sarif(results, secrets_findings, repo_path)
        sarif_file = os.path.join(repo_path, "argus_results.sarif")
        with open(sarif_file, "w") as f:
            json.dump(sarif_data, f, indent=2)
        print(f"SARIF report written to: {sarif_file}")
    except Exception as e:
        print(f"Error generating SARIF report: {e}")
    
    # 4. Create PR if there are fixes
    if all_fixed_content:
        pr_url = create_remediation_pr(all_fixed_content, all_proofs)
        if pr_url:
            print(f"\n🚀 Argus Auto-Remediation PR Created: {pr_url}")
        else:
            print("\n⚠️ Could not create auto-remediation PR")
    else:
        print("\n📝 No fixes to submit (all files secure or unfixable)")
    
    # 5. Final status
    if exit_code == 0:
        print("\n✅ Audit PASSED")
    else:
        print("\n❌ Audit FAILED - Some vulnerabilities could not be fixed")
        
    sys.exit(exit_code)


if __name__ == "__main__":
    main()
