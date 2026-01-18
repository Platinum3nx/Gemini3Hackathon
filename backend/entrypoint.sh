#!/bin/bash
set -e
# If arguments are passed, run them (allows overriding command)
if [ "$#" -gt 0 ]; then
    exec "$@"
fi
# Default Action behavior: Run the CI Runner
echo "Starting Argus AI Auditor..."
# GitHub Actions mounts the user's code at /github/workspace
# We need to tell our runner where that is.
export REPO_PATH="/github/workspace"
# Run the python script
python3 -m backend.ci_runner
