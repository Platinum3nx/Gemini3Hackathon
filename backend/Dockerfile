FROM python:3.11-slim

# Install system dependencies for Lean 4 (elan)
RUN apt-get update && apt-get install -y \
    git \
    curl \
    build-essential \
    libgmp-dev \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean Version Manager)
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
ENV PATH="/root/.elan/bin:$PATH"

# Install Lean 4 stable
RUN elan default stable

# Set working directory to /app
WORKDIR /app

# Copy requirements.txt and install Python dependencies
# Context is usually the 'backend' folder now, so we copy valid files from there.
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Copy everything in the current directory (backend/) to /app/backend
# This puts main.py, agents.py etc into /app/backend, restoring package structure
COPY . ./backend

# Expose port
EXPOSE 8000

# Set PYTHONPATH to /app so 'backend' package is found
ENV PYTHONPATH=/app

# Copy entrypoint script for GitHub Actions
COPY entrypoint.sh /app/backend/entrypoint.sh
RUN chmod +x /app/backend/entrypoint.sh

# Run commands
# Running from /app, "backend.main" as module.
CMD ["uvicorn", "backend.main:app", "--host", "0.0.0.0", "--port", "8000"]
