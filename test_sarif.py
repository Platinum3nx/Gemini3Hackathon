
import json
from backend.sarif_generator import generate_sarif
from backend.secrets_scanner import SecretFinding

# Mock Audit Results
audit_results = [
    {
        "filename": "vulnerable_file.py",
        "status": "VULNERABLE",
        "proof": "omega could not prove: balance >= 0"
    },
    {
        "filename": "secure_file.py",
        "status": "SECURE"
    }
]

# Mock Secrets
secrets = [
    SecretFinding(
        file_path="config.py",
        line_number=10,
        secret_type="AWS Access Key ID",
        matched_text="AKIA****************",
        severity="HIGH",
        description="AWS Access Key detected"
    )
]

# Generate SARIF
sarif = generate_sarif(audit_results, secrets, ".")
print(json.dumps(sarif, indent=2))
