#!/bin/sh
set -e

if [ "$#" -gt 0 ]; then
    exec "$@"
fi

echo "Starting Argus AI Auditor..."
export REPO_PATH="/github/workspace"

# Run the module
python3 -m backend.ci_runner
