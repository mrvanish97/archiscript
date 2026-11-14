#!/usr/bin/env bash
set -euo pipefail
exec uv run --no-project python scripts/check-lean-negative.py
