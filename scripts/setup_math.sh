#!/usr/bin/env bash
set -euo pipefail
NT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
python3 -m venv "$NT_ROOT/.tools/math-python"
"$NT_ROOT/.tools/math-python/bin/python" -m pip install -r "$NT_ROOT/scripts/math-requirements.txt"
"$NT_ROOT/.tools/math-python/bin/python" -c 'import sympy; print("SymPy", sympy.__version__)'
