#!/bin/bash
set -e

# If arguments are passed, run them
if [ "$#" -gt 0 ]; then
    exec "$@"
fi

echo "Starting Argus AI Auditor..."
export REPO_PATH="/github/workspace"

# Run using System Python (prevents venv errors)
python3 -m backend.ci_runner
