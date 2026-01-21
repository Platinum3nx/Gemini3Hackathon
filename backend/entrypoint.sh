#!/bin/bash
set -e
if [ "$#" -gt 0 ]; then
    exec "$@"
fi
echo "Starting Argus AI Auditor..."
export REPO_PATH="/github/workspace"
python3 -m backend.ci_runner
