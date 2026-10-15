#!/usr/bin/env bash
set -euo pipefail
NT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$NT_ROOT"
python3 scripts/check_integrity.py
scripts/with_lean.sh lake build
scripts/with_lean.sh python3 scripts/audit_axioms.py
