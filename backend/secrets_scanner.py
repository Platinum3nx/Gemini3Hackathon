"""
Secrets Scanner - Detects leaked API keys, passwords, and tokens.

This module scans code files for common secret patterns like:
- API keys (AWS, Google, OpenAI, etc.)
- Passwords in code
- Private keys
- Tokens (GitHub, Slack, etc.)
"""
import re
import os
from typing import List, Dict, Any
from dataclasses import dataclass


@dataclass
class SecretFinding:
    """Represents a detected secret in code."""
    file_path: str
    line_number: int
    secret_type: str
    matched_text: str  # Redacted version
    severity: str  # HIGH, MEDIUM, LOW
    description: str


# Secret patterns with their metadata
# Each pattern: (name, regex, severity, description)
SECRET_PATTERNS = [
    # AWS
    (
        "AWS Access Key ID",
        r"(?:A3T[A-Z0-9]|AKIA|AGPA|AIDA|AROA|AIPA|ANPA|ANVA|ASIA)[A-Z0-9]{16}",
        "HIGH",
        "AWS Access Key ID detected. Rotate immediately."
    ),
    (
        "AWS Secret Access Key",
        r"(?i)aws[_\-\.]?secret[_\-\.]?(?:access)?[_\-\.]?key[\s]*[=:]+[\s]*['\"]?([a-zA-Z0-9/+=]{40})['\"]?",
        "HIGH",
        "AWS Secret Access Key detected. Rotate immediately."
    ),
    
    # Google
    (
        "Google API Key",
        r"AIza[0-9A-Za-z\-_]{35}",
        "HIGH",
        "Google API Key detected. Restrict or rotate."
    ),
    (
        "Google OAuth Client Secret",
        r"(?i)client[_\-]?secret[\s]*[=:]+[\s]*['\"]?([a-zA-Z0-9_\-]{24})['\"]?",
        "MEDIUM",
        "Possible Google OAuth client secret."
    ),
    
    # GitHub
    (
        "GitHub Personal Access Token",
        r"ghp_[a-zA-Z0-9]{36}",
        "HIGH",
        "GitHub PAT detected. Revoke and regenerate."
    ),
    (
        "GitHub OAuth Access Token",
        r"gho_[a-zA-Z0-9]{36}",
        "HIGH",
        "GitHub OAuth token detected."
    ),
    (
        "GitHub App Token",
        r"(?:ghu|ghs)_[a-zA-Z0-9]{36}",
        "HIGH",
        "GitHub App token detected."
    ),
    (
        "GitHub Refresh Token",
        r"ghr_[a-zA-Z0-9]{36}",
        "HIGH",
        "GitHub refresh token detected."
    ),
    
    # OpenAI
    (
        "OpenAI API Key",
        r"sk-[a-zA-Z0-9]{48}",
        "HIGH",
        "OpenAI API key detected. Rotate immediately."
    ),
    
    # Slack
    (
        "Slack Bot Token",
        r"xoxb-[0-9]{10,13}-[0-9]{10,13}-[a-zA-Z0-9]{24}",
        "HIGH",
        "Slack bot token detected."
    ),
    (
        "Slack User Token",
        r"xoxp-[0-9]{10,13}-[0-9]{10,13}-[a-zA-Z0-9]{24}",
        "HIGH",
        "Slack user token detected."
    ),
    (
        "Slack Webhook URL",
        r"https://hooks\.slack\.com/services/T[a-zA-Z0-9_]+/B[a-zA-Z0-9_]+/[a-zA-Z0-9_]+",
        "MEDIUM",
        "Slack webhook URL detected."
    ),
    
    # Stripe
    (
        "Stripe API Key",
        r"(?:sk|pk)_(?:live|test)_[a-zA-Z0-9]{24,}",
        "HIGH",
        "Stripe API key detected. Rotate if live key."
    ),
    
    # Generic Patterns
    (
        "Generic API Key",
        r"(?i)(?:api[_\-\.]?key|apikey)[\s]*[=:]+[\s]*['\"]([a-zA-Z0-9_\-]{20,})['\"]",
        "MEDIUM",
        "Possible API key detected."
    ),
    (
        "Generic Secret",
        r"(?i)(?:secret|token|password|passwd|pwd)[\s]*[=:]+[\s]*['\"]([^\s'\"]{8,})['\"]",
        "MEDIUM",
        "Possible secret or password in code."
    ),
    (
        "Private Key",
        r"-----BEGIN (?:RSA |EC |DSA |OPENSSH )?PRIVATE KEY-----",
        "HIGH",
        "Private key detected. Never commit private keys!"
    ),
    (
        "JWT Token",
        r"eyJ[a-zA-Z0-9_-]*\.eyJ[a-zA-Z0-9_-]*\.[a-zA-Z0-9_-]*",
        "MEDIUM",
        "JWT token detected. May contain sensitive claims."
    ),
    
    # Database
    (
        "Database URL with Password",
        r"(?i)(?:postgres|mysql|mongodb|redis)://[^:]+:([^@]+)@",
        "HIGH",
        "Database connection string with password detected."
    ),
]


def _redact_secret(text: str, keep_chars: int = 4) -> str:
    """Redact a secret, keeping only first few characters."""
    if len(text) <= keep_chars * 2:
        return "*" * len(text)
    return text[:keep_chars] + "*" * (len(text) - keep_chars * 2) + text[-keep_chars:]


def scan_file(file_path: str, content: str = None) -> List[SecretFinding]:
    """
    Scan a single file for secrets.
    
    Args:
        file_path: Path to the file
        content: Optional file content (if not provided, reads from disk)
        
    Returns:
        List of SecretFinding objects
    """
    findings = []
    
    if content is None:
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
        except Exception as e:
            print(f"[Secrets Scanner] Error reading {file_path}: {e}")
            return []
    
    lines = content.split('\n')
    
    for pattern_name, pattern_regex, severity, description in SECRET_PATTERNS:
        try:
            regex = re.compile(pattern_regex)
            
            for line_num, line in enumerate(lines, start=1):
                matches = regex.finditer(line)
                for match in matches:
                    # Get the matched text
                    matched_text = match.group(0)
                    
                    # Skip if it looks like a placeholder or example
                    if _is_placeholder(matched_text):
                        continue
                    
                    finding = SecretFinding(
                        file_path=file_path,
                        line_number=line_num,
                        secret_type=pattern_name,
                        matched_text=_redact_secret(matched_text),
                        severity=severity,
                        description=description
                    )
                    findings.append(finding)
                    
        except re.error as e:
            print(f"[Secrets Scanner] Regex error for {pattern_name}: {e}")
            continue
    
    return findings


def _is_placeholder(text: str) -> bool:
    """Check if the matched text looks like a placeholder/example."""
    placeholders = [
        "your_api_key",
        "your_secret",
        "xxx",
        "example",
        "placeholder",
        "insert_",
        "replace_",
        "<your",
        "${",
        "{{",
        "env.",
        "os.getenv",
        "os.environ",
        "process.env",
    ]
    text_lower = text.lower()
    return any(p in text_lower for p in placeholders)


def scan_repo(repo_path: str) -> List[SecretFinding]:
    """
    Scan all files in a repository for secrets.
    
    Args:
        repo_path: Path to the repository root
        
    Returns:
        List of all SecretFinding objects across all files
    """
    print(f"[Secrets Scanner] Scanning repository: {repo_path}")
    
    all_findings = []
    files_scanned = 0
    
    # File extensions to scan
    scan_extensions = {
        '.py', '.js', '.ts', '.jsx', '.tsx', '.java', '.go', '.rb', '.php',
        '.yaml', '.yml', '.json', '.xml', '.env', '.conf', '.config',
        '.sh', '.bash', '.zsh', '.sql', '.md', '.txt'
    }
    
    # Directories to skip
    skip_dirs = {
        '.git', 'node_modules', '__pycache__', 'venv', 'env', '.venv',
        'dist', 'build', '.next', 'coverage', '.pytest_cache'
    }
    
    for root, dirs, files in os.walk(repo_path):
        # Skip ignored directories
        dirs[:] = [d for d in dirs if d not in skip_dirs]
        
        for file in files:
            # Check extension
            _, ext = os.path.splitext(file)
            if ext.lower() not in scan_extensions and file not in {'.env', '.envrc'}:
                continue
            
            file_path = os.path.join(root, file)
            rel_path = os.path.relpath(file_path, repo_path)
            
            findings = scan_file(file_path)
            if findings:
                # Update file_path to relative for cleaner output
                for f in findings:
                    f.file_path = rel_path
                all_findings.extend(findings)
            
            files_scanned += 1
    
    print(f"[Secrets Scanner] Scanned {files_scanned} files, found {len(all_findings)} potential secrets")
    return all_findings


def format_findings_for_report(findings: List[SecretFinding]) -> str:
    """Format findings for the audit report."""
    if not findings:
        return ""
    
    lines = ["## 🔐 Secrets Detection\n"]
    lines.append(f"**{len(findings)} potential secret(s) detected**\n")
    
    # Group by severity
    high = [f for f in findings if f.severity == "HIGH"]
    medium = [f for f in findings if f.severity == "MEDIUM"]
    
    if high:
        lines.append("### 🔴 High Severity\n")
        for f in high:
            lines.append(f"- **{f.secret_type}** in `{f.file_path}` (line {f.line_number})")
            lines.append(f"  - Matched: `{f.matched_text}`")
            lines.append(f"  - {f.description}\n")
    
    if medium:
        lines.append("### 🟡 Medium Severity\n")
        for f in medium:
            lines.append(f"- **{f.secret_type}** in `{f.file_path}` (line {f.line_number})")
            lines.append(f"  - Matched: `{f.matched_text}`")
            lines.append(f"  - {f.description}\n")
    
    return "\n".join(lines)


if __name__ == "__main__":
    # Test the scanner
    import sys
    
    if len(sys.argv) > 1:
        path = sys.argv[1]
        if os.path.isfile(path):
            findings = scan_file(path)
        else:
            findings = scan_repo(path)
        
        if findings:
            print("\n" + format_findings_for_report(findings))
        else:
            print("No secrets detected!")
    else:
        print("Usage: python secrets_scanner.py <file_or_directory>")
