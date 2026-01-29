# Argus 🛡️
## Neuro-Symbolic AI Security Auditor

**Mathematically Verified Code Repair Powered by Gemini 3 + Lean 4**

Argus is a GitHub Action that combines the creativity of **Gemini 3** with the rigor of **Lean 4 formal proofs** to automatically find AND fix security vulnerabilities in Python code.

> **100% Reliable** — Not because we avoid AI, but because every AI-generated fix is **mathematically verified** before being accepted.

---

## 🧠 Neuro-Symbolic Architecture

Argus uses a **Neuro-Symbolic Repair Loop** that combines:

| Component | Role | Strength |
|-----------|------|----------|
| **Lean 4** (Symbolic) | Formal verification | 100% reliable proofs |
| **Gemini 3** (Neural) | Code understanding & repair | Creative problem-solving |

The key insight: **AI proposes, Math verifies.** Gemini generates fixes, but Lean 4 proves they're correct.

---

## 🔄 How It Works

### The Neuro-Symbolic Repair Loop

```
                    ┌─────────────────────────────────────────────┐
                    │           ARGUS WORKFLOW                     │
                    └─────────────────────────────────────────────┘

                              ┌──────────────┐
                              │ Python Code  │
                              │ (Your Repo)  │
                              └──────┬───────┘
                                     │
                                     ▼
                         ┌───────────────────────┐
                         │   AST Translation     │
                         │   (Python → Lean 4)   │
                         └───────────┬───────────┘
                                     │
                                     ▼
                    ┌────────────────────────────────┐
                    │                                │
                    │         LEAN 4 PROVER          │
                    │    (Formal Verification)       │
                    │                                │
                    └────────────┬───────────────────┘
                                 │
                    ┌────────────┴────────────┐
                    │                         │
                    ▼                         ▼
            ┌─────────────┐           ┌─────────────┐
            │  ✅ PROOF   │           │  ❌ PROOF   │
            │   PASSED    │           │   FAILED    │
            └──────┬──────┘           └──────┬──────┘
                   │                         │
                   ▼                         ▼
            ┌─────────────┐    ┌─────────────────────────┐
            │   SECURE    │    │      GEMINI 3           │
            │   (Done!)   │    │  "Why did this fail?"   │
            └─────────────┘    │  "Generate a fix..."    │
                               └───────────┬─────────────┘
                                           │
                                           ▼
                               ┌───────────────────────┐
                               │   Fixed Python Code   │
                               │   (AI-Generated)      │
                               └───────────┬───────────┘
                                           │
                                           ▼
                               ┌───────────────────────┐
                               │      LEAN 4 PROVER    │
                               │   (Verify the Fix)    │
                               └───────────┬───────────┘
                                           │
                              ┌────────────┴────────────┐
                              │                         │
                              ▼                         ▼
                      ┌─────────────┐           ┌─────────────┐
                      │  ✅ PROOF   │           │  ❌ PROOF   │
                      │   PASSED    │           │   FAILED    │
                      └──────┬──────┘           └──────┬──────┘
                             │                         │
                             ▼                         ▼
                      ┌─────────────┐           ┌─────────────┐
                      │ AUTO_PATCHED│           │ VULNERABLE  │
                      │  (Success!) │           │ (AI Failed) │
                      └─────────────┘           └─────────────┘
```

### The 4-Step Process

1. **Translate** — Deterministic AST parser converts Python → Lean 4
2. **Verify** — Lean 4 attempts to prove safety properties
3. **Repair** — If proof fails, Gemini 3 analyzes the error and generates a fix
4. **Re-Verify** — Lean 4 proves the fix is correct (no hallucinations accepted!)

---

## 🤖 Gemini 3 Integration

Argus leverages **Gemini 3** for intelligent code analysis and repair:

### Automated Code Repair
When Lean 4 detects a vulnerability, Gemini 3 acts as a **Formal Verification Security Engineer**:

- **Analyzes** the Lean error message to understand why the proof failed
- **Identifies** missing guards, checks, or edge cases
- **Generates** a corrected version of the Python code
- **Preserves** function signatures and original intent

### Error Explanation
Gemini 3 interprets cryptic Lean 4 errors into actionable insights:

```
Lean Error: "omega could not prove: balance - amount ≥ 0"
     ↓
Gemini: "The withdraw function can return negative balance. 
         Add a guard: if amount > balance, return balance unchanged."
```

### Why Neuro-Symbolic?

| Pure AI Approach | Pure Formal Methods | **Argus (Neuro-Symbolic)** |
|------------------|--------------------|-----------------------------|
| Fast but unreliable | Reliable but can't fix | Fast, reliable, AND fixes bugs |
| Hallucinations possible | No code generation | AI generates, Math verifies |
| "Probably correct" | "Correct but still broken" | **"Provably fixed"** |

---

## 🚀 Quick Start

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

Argus will automatically audit Python files and attempt to fix any vulnerabilities.

---

## 📊 Example Output

```
Argus AI Audit Report

Summary
• Total Files Audited: 2
• ✅ Secure: 1
• 🔧 Auto-Patched: 1
• ❌ Vulnerable: 0

Details

🔧 wallet_buggy.py
Status: AUTO_PATCHED
🔧 Repair Attempt: SUCCESS
- Fixed file: wallet_buggy_fixed.py
▶ View Fix
▶ View Formal Proof (Lean 4)

✅ wallet_secure.py  
Status: SECURE
▶ View Formal Proof (Lean 4)
```

---

## 🏗️ Architecture Components

| Component | File | Purpose |
|-----------|------|---------|
| **CI Runner** | `ci_runner.py` | Orchestrates audit + repair loop |
| **AST Translator** | `python_to_lean.py` | Python → Lean 4 (deterministic) |
| **Lean Driver** | `lean_driver.py` | Runs Lean compiler, captures results |
| **AI Repair** | `ai_repair.py` | Gemini-powered code repair |
| **Agents** | `agents.py` | File auditing logic |

---

## 🔒 Why It's Reliable

**The Math Can't Lie**

Even though Gemini 3 generates fixes, every fix is verified by Lean 4 before being accepted:

| Step | Tool | Can Hallucinate? |
|------|------|------------------|
| Translation | Python AST | No (deterministic) |
| Verification | Lean 4 | No (mathematical proof) |
| Repair | Gemini 3 | **Yes** |
| Re-Verification | Lean 4 | No (catches hallucinations) |

If Gemini's fix is wrong, Lean 4 rejects it. **No hallucination can pass the prover.**

---

## ⚠️ Current Limitations

- Supports basic Python constructs (functions, if/else, arithmetic, comparisons)
- Focused on financial safety properties (balance ≥ 0)
- Single repair attempt per file (no retry loop yet)

---

## 🛠️ Tech Stack

- **Python 3.11** — Backend and AST parsing
- **Lean 4.26.0** — Formal verification
- **Mathlib** — Lean tactics library
- **Gemini 3** — AI-powered code repair
- **Docker** — GitHub Action container
- **GitHub Actions** — CI/CD integration

---

## 📜 License

MIT License — see [LICENSE](LICENSE) for details.

---

Built for the **2026 Gemini 3 Hackathon** 🚀

*"AI proposes, Math verifies."*
