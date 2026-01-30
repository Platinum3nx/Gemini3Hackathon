"""
GitHub Service Module - Auto-Remediation PR Creation

This module handles the automatic creation of Pull Requests containing
verified security fixes. Each PR includes the patched code and the
formal Lean 4 proofs that mathematically guarantee the fix is correct.

The Neuro-Symbolic workflow:
1. Gemini 3 proposes fixes for vulnerable code
2. Lean 4 verifies these fixes are mathematically safe
3. This module creates a PR with the verified fixes
4. User reviews proofs and merges with one click
"""

import os
import time
from datetime import datetime
from typing import Dict, Optional
from github import Github, GithubException


class GitHubService:
    """
    Service for creating auto-remediation Pull Requests.
    
    Uses PyGithub to authenticate and interact with the GitHub API.
    """
    
    def __init__(self, token: Optional[str] = None):
        """
        Initialize the GitHub service.
        
        Args:
            token: GitHub token (defaults to GITHUB_TOKEN env var)
        """
        self.token = token or os.getenv("GITHUB_TOKEN")
        if not self.token:
            raise ValueError("GITHUB_TOKEN environment variable not set")
        
        self.client = Github(self.token)
    
    def _sanitize_branch_name(self, name: str) -> str:
        """
        Sanitize a string to be a valid git branch name.
        
        Removes or replaces invalid characters.
        """
        import re
        # Replace spaces and invalid chars with hyphens
        sanitized = re.sub(r'[^a-zA-Z0-9/_-]', '-', name)
        # Remove consecutive hyphens
        sanitized = re.sub(r'-+', '-', sanitized)
        # Remove leading/trailing hyphens
        sanitized = sanitized.strip('-')
        return sanitized
    
    def create_fix_pr(
        self,
        repo_name: str,
        original_branch: str,
        fixes: Dict[str, str],
        proofs: Dict[str, str]
    ) -> str:
        """
        Create a Pull Request containing verified security fixes.
        
        Args:
            repo_name: Repository string (e.g. "user/repo")
            original_branch: The branch the user pushed to (e.g., "main", "feat/login")
            fixes: Dict mapping filenames to fixed code content
            proofs: Dict mapping filenames to Lean 4 proof text
            
        Returns:
            URL of the created Pull Request
        """
        print(f"[GitHub Service] Creating fix PR for {repo_name}")
        print(f"[GitHub Service] Target branch: {original_branch}")
        
        # Get the repository
        repo = self.client.get_repo(repo_name)
        
        # Generate dynamic branch name based on the feature branch
        # e.g., "feat/login" becomes "feat/login-ArgusVerified"
        fix_branch = self._sanitize_branch_name(f"{original_branch}-ArgusVerified")
        
        print(f"[GitHub Service] Creating branch: {fix_branch}")
        
        # Get the SHA of the original branch
        try:
            original_ref = repo.get_branch(original_branch)
            base_sha = original_ref.commit.sha
        except GithubException as e:
            raise RuntimeError(f"Could not find branch '{original_branch}': {e}")
        
        # Create the new branch
        try:
            repo.create_git_ref(
                ref=f"refs/heads/{fix_branch}",
                sha=base_sha
            )
            print(f"[GitHub Service] Branch {fix_branch} created from {original_branch}")
        except GithubException as e:
            raise RuntimeError(f"Could not create branch '{fix_branch}': {e}")
        
        # Commit all fixed files to the new branch
        print(f"[GitHub Service] Committing {len(fixes)} fixed files...")
        
        for filename, fixed_code in fixes.items():
            try:
                # Check if file exists
                try:
                    existing_file = repo.get_contents(filename, ref=fix_branch)
                    # Update existing file
                    repo.update_file(
                        path=filename,
                        message=f"fix: Apply verified security fix to {filename}\n\nThis fix has been mathematically verified using Lean 4 formal proofs.",
                        content=fixed_code,
                        sha=existing_file.sha,
                        branch=fix_branch
                    )
                    print(f"[GitHub Service] Updated: {filename}")
                except GithubException:
                    # File doesn't exist, create it
                    repo.create_file(
                        path=filename,
                        message=f"fix: Add verified security fix {filename}\n\nThis fix has been mathematically verified using Lean 4 formal proofs.",
                        content=fixed_code,
                        branch=fix_branch
                    )
                    print(f"[GitHub Service] Created: {filename}")
                    
            except GithubException as e:
                print(f"[GitHub Service] Error committing {filename}: {e}")
                raise
        
        # Generate the PR body with proofs
        pr_body = self._generate_pr_body(fixes, proofs, original_branch)
        
        # Create the Pull Request with dynamic title
        print(f"[GitHub Service] Creating Pull Request targeting '{original_branch}'...")
        
        try:
            pr = repo.create_pull(
                title=f"🛡️ Argus Verified Fixes for `{original_branch}`",
                body=pr_body,
                head=fix_branch,
                base=original_branch
            )
            print(f"[GitHub Service] PR created: {pr.html_url}")
            return pr.html_url
            
        except GithubException as e:
            error_msg = str(e)
            
            # Check for the specific "not permitted to create PRs" error
            if "GitHub Actions is not permitted" in error_msg or "pull requests" in error_msg.lower():
                print("")
                print("╔" + "═" * 60 + "╗")
                print("║" + " ⚠️  PR CREATION BLOCKED BY REPO SETTINGS".center(60) + "║")
                print("╠" + "═" * 60 + "╣")
                print("║" + "".center(60) + "║")
                print("║" + " To fix this:".ljust(60) + "║")
                print("║" + "".center(60) + "║")
                print("║" + " 1. Go to Repo Settings > Actions > General".ljust(60) + "║")
                print("║" + " 2. Scroll to 'Workflow permissions'".ljust(60) + "║")
                print("║" + " 3. Check 'Allow GitHub Actions to create and".ljust(60) + "║")
                print("║" + "    approve pull requests'".ljust(60) + "║")
                print("║" + "".center(60) + "║")
                print("║" + " Then re-run this workflow.".ljust(60) + "║")
                print("║" + "".center(60) + "║")
                print("╚" + "═" * 60 + "╝")
                print("")
                # Return None instead of crashing
                return None
            
            # For other errors, raise as before
            raise RuntimeError(f"Could not create PR: {e}")
    
    def _generate_pr_body(
        self,
        fixes: Dict[str, str],
        proofs: Dict[str, str],
        base_branch: str = "main"
    ) -> str:
        """
        Generate the PR description with formal proofs.
        
        Args:
            fixes: Dict mapping filenames to fixed code content
            proofs: Dict mapping filenames to Lean 4 proof text
            base_branch: The target branch for this PR
            
        Returns:
            Markdown-formatted PR body
        """
        lines = [
            f"# 🛡️ Argus Auto-Remediation Report for `{base_branch}`",
            "",
            "This Pull Request contains **verified security fixes** generated by [Argus](https://github.com/Platinum3nx/Argus).",
            "",
            f"> 🎯 **Target Branch:** `{base_branch}`",
            "",
            "## 🔒 What is this?",
            "",
            "Argus detected vulnerabilities in your code and automatically generated fixes. Each fix has been:",
            "",
            "1. **Proposed** by Gemini 3 (AI-powered code repair)",
            "2. **Verified** by Lean 4 (mathematical proof of correctness)",
            "",
            "> ✅ These fixes are not just AI suggestions—they are **mathematically proven** to satisfy safety invariants.",
            "",
            "---",
            "",
            "## 📝 Fixed Files",
            "",
        ]
        
        for filename in fixes.keys():
            proof = proofs.get(filename, "Proof not available")
            
            lines.extend([
                f"### `{filename}`",
                "",
                "<details>",
                "<summary>🔍 View Verified Safety Proof (Lean 4)</summary>",
                "",
                "```lean",
                proof,
                "```",
                "",
                "</details>",
                "",
            ])
        
        lines.extend([
            "---",
            "",
            "## ✅ How to Review",
            "",
            "1. **Check the Diff** — Review the code changes in the Files tab",
            "2. **Verify the Proofs** — Each file has a collapsible Lean 4 proof showing the mathematical guarantee",
            "3. **Merge with Confidence** — These fixes are proven correct, not just tested",
            "",
            "---",
            "",
            "*Generated by [Argus](https://github.com/Platinum3nx/Argus) — Neuro-Symbolic AI Security Auditor*",
            "",
            "*\"AI proposes, Math verifies.\"*",
        ])
        
        return "\n".join(lines)


# --- TEST ---
if __name__ == "__main__":
    print("GitHubService module loaded.")
    print("To test, set GITHUB_TOKEN and call create_fix_pr()")
