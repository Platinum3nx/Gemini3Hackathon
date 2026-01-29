# Argus 🛡️

**Formal Verification for Python Security**

Argus is a GitHub Action that uses **Lean 4 mathematical proofs** to verify Python code security. Unlike traditional static analyzers that use heuristics, Argus provides **100% reliable verdicts** by translating Python to Lean 4 and attempting to prove safety properties.

---

## How It Works

### The 3-Step Process

1. **Deterministic Translation** (Python → Lean 4)
   - Uses Python's AST parser (no AI involved)
   - Converts functions exactly as written - preserves bugs
   - Generates a safety theorem template

2. **Formal Verification** (Lean 4 Compiler)
   - Runs `split_ifs` to analyze all code branches
   - Runs `omega` to prove arithmetic properties
   - Returns pass/fail for the proof

3. **Verdict**
   - ✅ **SECURE**: Proof passed - mathematically guaranteed safe
   - ❌ **VULNERABLE**: Proof failed - safety property violated

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         ARGUS WORKFLOW                                  │
└─────────────────────────────────────────────────────────────────────────┘

    GitHub Push
         │
         ▼
┌─────────────────┐
│  Your Repo      │
│  (Python code)  │
└────────┬────────┘
         │
         ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                    ARGUS GITHUB ACTION                                  │
│                                                                          │
│  ┌──────────────┐    ┌──────────────────┐    ┌───────────────┐          │
│  │ Python Code  │───▶│  AST Translator  │───▶│  Lean 4 Code  │          │
│  │              │    │  (python_to_lean)│    │  + Theorem    │          │
│  │ def withdraw │    │                  │    │               │          │
│  │   (balance,  │    │  100% Reliable   │    │ def withdraw  │          │
│  │    amount):  │    │  No AI/LLM       │    │   := ...      │          │
│  │   return ... │    │                  │    │               │          │
│  └──────────────┘    └──────────────────┘    │ theorem       │          │
│                                               │   verify_     │          │
│                                               │   safety ...  │          │
│                                               └───────┬───────┘          │
│                                                       │                  │
│                                                       ▼                  │
│                                              ┌───────────────┐           │
│                                              │  Lean 4       │           │
│                                              │  Compiler     │           │
│                                              │  + Mathlib    │           │
│                                              └───────┬───────┘           │
│                                                      │                   │
│                           ┌──────────────────────────┴───┐               │
│                           ▼                              ▼               │
│                    ┌────────────┐               ┌────────────┐           │
│                    │ Proof PASS │               │ Proof FAIL │           │
│                    └─────┬──────┘               └─────┬──────┘           │
│                          ▼                            ▼                  │
│                    ┌────────────┐               ┌────────────┐           │
│                    │  ✅ SECURE │               │❌VULNERABLE│           │
│                    └────────────┘               └────────────┘           │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
         │
         ▼
    GitHub Actions Summary
    (visible in PR/commit)
```

---

## Quick Start

### 1. Add the GitHub Action to your repo

Create `.github/workflows/argus_audit.yml`:

```yaml
name: Argus Security Audit

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

jobs:
  argus-check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0
      
      - name: Run Argus AI Auditor
        uses: Platinum3nx/Argus@main
        with:
          gemini_api_key: ${{ secrets.GEMINI_API_KEY }}
```

### 2. Add your Gemini API Key

1. Go to your repo → Settings → Secrets and variables → Actions
2. Add a new secret: `GEMINI_API_KEY`
3. Get your key from [Google AI Studio](https://aistudio.google.com/apikey)

### 3. Push code and see results!

Argus will automatically audit Python files on every push and show results in the GitHub Actions summary.

---

## Example Output

```
Argus AI Audit Report

Summary
• Total Files Audited: 2
• ✅ Secure: 1
• ❌ Vulnerable: 1

Details

❌ wallet_buggy.py
Status: VULNERABLE
▶ View Formal Proof (Lean 4)

✅ wallet_secure.py  
Status: SECURE
▶ View Formal Proof (Lean 4)
```

---

## Key Components

| Component | File | Purpose |
|-----------|------|---------|
| **CI Runner** | `ci_runner.py` | Orchestrates the audit process |
| **AST Translator** | `python_to_lean.py` | Converts Python → Lean 4 (deterministic) |
| **Theorem Generator** | `python_to_lean.py` | Creates safety theorem template |
| **Lean Driver** | `lean_driver.py` | Runs Lean compiler, captures results |
| **Report Generator** | `ci_runner.py` | Creates GitHub Actions summary |

---

## Why Argus?

**The key insight:** We use deterministic tools for what requires precision:

| Task | Tool | Reliability |
|------|------|-------------|
| Parse Python syntax | Python AST | 100% |
| Translate to Lean | Rule-based converter | 100% |
| Prove safety | Lean 4 compiler | 100% |
| Interpret results | Simple if/else | 100% |

**Result:** A security tool that gives **mathematically guaranteed verdicts**, not probabilistic guesses.

---

## Current Limitations

- Supports basic Python constructs (functions, if/else, arithmetic, comparisons)
- Focused on financial safety properties (balance ≥ 0)
- Requires Lean 4 and Mathlib (included in Docker image)

---

## Tech Stack

- **Python 3.11** - Backend and AST parsing
- **Lean 4.26.0** - Formal verification
- **Mathlib** - Lean tactics library
- **Docker** - GitHub Action container
- **GitHub Actions** - CI/CD integration

---

## License

MIT License - see [LICENSE](LICENSE) for details.

---

Built for the **2026 Gemini 3 Hackathon** 🚀
