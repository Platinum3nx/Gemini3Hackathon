#!/bin/sh
set -e

# Map the GitHub Action input to the variable Argus expects
if [ -n "$INPUT_GEMINI_API_KEY" ]; then
    export GEMINI_API_KEY="$INPUT_GEMINI_API_KEY"
fi

if [ "$#" -gt 0 ]; then
    exec "$@"
fi

echo "Starting Argus AI Auditor..."
export REPO_PATH="/github/workspace"

# Run the module
python3 -m backend.ci_runner
