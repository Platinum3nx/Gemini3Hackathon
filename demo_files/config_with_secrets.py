"""
Example Configuration - DEMO FILE FOR TESTING SECRETS DETECTION

This file contains intentionally hardcoded secrets to demonstrate
Argus's secrets scanning capability. DO NOT USE IN PRODUCTION.
"""

# These are FAKE secrets for demo purposes only!
# Argus will detect these and flag them in the audit report.

# AWS Credentials (FAKE - Matches regex but safe for git)
AWS_ACCESS_KEY = "AKIAEXAMPLE123456789"
AWS_SECRET_KEY = "wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY"

# OpenAI API Key (FAKE)
OPENAI_API_KEY = "sk-EXAMPLE1234567890abcdefghijklmnopqrstuvwxyz0123"

# GitHub Personal Access Token (FAKE)
GITHUB_TOKEN = "ghp_EXAMPLE12345678901234567890123456789"

# Database connection with password (FAKE)
DATABASE_URL = "postgres://admin:EXAMPLEPASSWORD@localhost:5432/mydb"

# Stripe API Key (FAKE)
STRIPE_API_KEY = "sk_live_EXAMPLE1234567890abcdef"

# Generic password in code (FAKE)
admin_password = "MySecretPassword123!"


def get_config():
    """Return configuration - DO NOT DO THIS IN REAL CODE!"""
    return {
        "aws_key": AWS_ACCESS_KEY,
        "openai_key": OPENAI_API_KEY,
        "github_token": GITHUB_TOKEN,
    }
