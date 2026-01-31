"""
SARIF Generator - Converts Argus audit results into SARIF format.

Standard: SARIF v2.1.0
Schema: https://json.schemastore.org/sarif-2.1.0.json

Produces a report compatible with GitHub Code Scanning.
"""

import json
import os
from typing import List, Dict, Any

def generate_sarif(results: List[Dict[str, Any]], secrets_findings: List[Any], repo_path: str = ".") -> Dict[str, Any]:
    """
    Generate a SARIF report from Argus audit results.
    
    Args:
        results: List of audit results from Argus agents
        secrets_findings: List of SecretFinding objects
        repo_path: Base path of the repository
        
    Returns:
        Dictionary representing the full SARIF JSON object
    """
    
    # 1. Define Tool & Driver
    tool = {
        "driver": {
            "name": "Argus",
            "informationUri": "https://github.com/Platinum3nx/Argus",
            "semanticVersion": "1.0.0",
            "rules": [
                {
                    "id": "ARGUS001",
                    "name": "LogicVulnerability",
                    "shortDescription": {
                        "text": "Formal Verification Failed"
                    },
                    "fullDescription": {
                        "text": "The code failed to satisfy the required safety invariants (e.g., non-negative balance, unique list items) as proven by Lean 4."
                    },
                    "defaultConfiguration": {
                        "level": "error"
                    },
                    "help": {
                        "text": "Argus uses formal verification to prove code correctness. This error means specific safety properties (like preventing negative balances) could not be proven.",
                        "markdown": "# Formal Verification Failed\nArgus uses **Lean 4** to mathematically prove code correctness. This error indicates that the code violates a required invariant.\n\n## Remediation\nCheck the detailed error message to understand which condition failed. If Argus provided an auto-patch, review and merge it."
                    },
                    "properties": {
                        "tags": ["security", "formal-verification", "logic-error"]
                    }
                },
                {
                    "id": "ARGUS002",
                    "name": "SecretDetected",
                    "shortDescription": {
                        "text": "Hardcoded Secret Detected"
                    },
                    "fullDescription": {
                        "text": "A potential hardcoded secret (API key, password, token) was found in the codebase."
                    },
                    "defaultConfiguration": {
                        "level": "error"
                    },
                    "help": {
                        "text": "Hardcoded secrets can lead to unauthorized access. Rotate this secret immediately and use environment variables.",
                        "markdown": "# Hardcoded Secret Detected\nArgus detected a high-entropy string that matches a known secret pattern (e.g., AWS Key, API Token).\n\n## Remediation\n1. **Rotate** the secret immediately.\n2. **Remove** it from the code history.\n3. **Use** environment variables or a secrets manager."
                    },
                    "properties": {
                        "tags": ["security", "secrets", "cwe-798"]
                    }
                }
            ]
        }
    }
    
    sarif_results = []
    
    # 2. Process Logic Vulnerabilities
    for r in results:
        # We only report VULNERABLE items. 
        # AUTO_PATCHED and SECURE are essentially "passed" checks.
        if r.get("status") == "VULNERABLE":
            filename = r.get("filename")
            message = r.get("proof", "Verification failed")
            
            # Default line number to 1 if we can't parse it from the error
            # In a real impl, we'd parse the Lean error to find the exact line
            line_number = 1
            
            result_item = {
                "ruleId": "ARGUS001",
                "message": {
                    "text": f"Argus Logic Audit: {message}"
                },
                "level": "error",
                "locations": [
                    {
                        "physicalLocation": {
                            "artifactLocation": {
                                "uri": filename
                            },
                            "region": {
                                "startLine": line_number
                            }
                        }
                    }
                ]
            }
            sarif_results.append(result_item)

    # 3. Process Secrets
    if secrets_findings:
        for secret in secrets_findings:
            # Map severity to SARIF level
            level = "error" if secret.severity == "HIGH" else "warning"
            
            result_item = {
                "ruleId": "ARGUS002",
                "message": {
                    "text": f"Potential {secret.secret_type} detected: {secret.description}"
                },
                "level": level,
                "locations": [
                    {
                        "physicalLocation": {
                            "artifactLocation": {
                                "uri": secret.file_path
                            },
                            "region": {
                                "startLine": secret.line_number,
                                "snippet": {
                                    "text": secret.matched_text
                                }
                            }
                        }
                    }
                ]
            }
            sarif_results.append(result_item)

    # 4. Construct Final SARIF Object
    sarif_output = {
        "$schema": "https://json.schemastore.org/sarif-2.1.0.json",
        "version": "2.1.0",
        "runs": [
            {
                "tool": tool,
                "results": sarif_results,
                "invocations": [
                    {
                        "executionSuccessful": True
                    }
                ]
            }
        ]
    }
    
    return sarif_output
