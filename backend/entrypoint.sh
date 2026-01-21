#!/bin/bash
set -e

# If arguments are passed, run them
if [ "$#" -gt 0 ]; then
    exec "$@"
fi

# Default Action behavior
echo "Starting Argus AI Auditor..."

# GitHub Actions mounts the user's code at /github/workspace
# We tell the python script where to look
export REPO_PATH="/github/workspace"

# Run the python script using the SYSTEM python, not venv
python3 -m backend.ci_runner
