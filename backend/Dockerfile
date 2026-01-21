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

# 3. Install elan and Lean 4 stable into that global directory
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain stable

# 4. Explicitly set the default toolchain again to be safe
RUN elan default stable

# 5. Set working directory
WORKDIR /app

# 6. Install Python dependencies
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# 7. Copy backend code
COPY . ./backend

# 8. Create proofs directory (The fix from before)
RUN mkdir -p /app/veritas_proofs && chmod 777 /app/veritas_proofs

# 9. Setup environment
EXPOSE 8000
ENV PYTHONPATH=/app

# 10. Entrypoint
COPY entrypoint.sh /app/backend/entrypoint.sh
RUN chmod +x /app/backend/entrypoint.sh

CMD ["uvicorn", "backend.main:app", "--host", "0.0.0.0", "--port", "8000"]