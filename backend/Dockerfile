FROM python:3.11-slim

# 1. Install system dependencies
RUN apt-get update && apt-get install -y \
    git \
    curl \
    build-essential \
    libgmp-dev \
    && rm -rf /var/lib/apt/lists/*

# 2. Set ELAN_HOME to a global directory (Crucial for GitHub Actions)
ENV ELAN_HOME="/usr/local/elan"
ENV PATH="${ELAN_HOME}/bin:${PATH}"

# 3. Install elan and the specific Lean 4 version
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:v4.26.0

# 4. Set working directory
WORKDIR /app

# 5. Copy the veritas_proofs Lean project (now inside backend/)
COPY veritas_proofs ./veritas_proofs

# 6. Download Mathlib cache (required for split_ifs tactic)
WORKDIR /app/veritas_proofs
RUN lake update && lake exe cache get

# 7. Return to app directory
WORKDIR /app

# 8. Install Python dependencies
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# 9. Cache-bust: Change this version to force Docker to re-copy backend code
ARG BUILD_VERSION=2026-01-30-v1
RUN echo "Build version: ${BUILD_VERSION}"

# 10. Copy backend code (this will now always be fresh due to cache-bust above)
COPY . ./backend

# 10. Setup environment
EXPOSE 8000
ENV PYTHONPATH=/app

# 11. Entrypoint
RUN chmod +x /app/backend/entrypoint.sh

CMD ["uvicorn", "backend.main:app", "--host", "0.0.0.0", "--port", "8000"]