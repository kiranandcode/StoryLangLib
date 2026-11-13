#!/usr/bin/env bash
# StoryLangLib Studio: one command. Backend (FastAPI, reloads on Python edits;
# watches stories/ and pushes updates) + frontend (Vite, hot module reload).
#   studio/run.sh            ports: UI 5177, API 8765 (STUDIO_PORT, STUDIO_API_PORT)
set -euo pipefail
cd "$(dirname "$0")"
ROOT="$(cd .. && pwd)"
export STUDIO_PORT="${STUDIO_PORT:-5177}" STUDIO_API_PORT="${STUDIO_API_PORT:-8765}"

[ -x "$ROOT/.lake/build/bin/langlib" ] || (cd "$ROOT" && lake build)
if [ ! -x .venv/bin/uvicorn ]; then
  uv venv -q .venv && uv pip install -q --python .venv/bin/python fastapi "uvicorn[standard]" watchfiles
fi
[ -d web/node_modules ] || (cd web && npm install --silent)

.venv/bin/uvicorn server:app --reload --reload-include '*.py' --port "$STUDIO_API_PORT" --log-level warning &
API=$!
trap "kill $API 2>/dev/null" EXIT INT TERM
echo "StoryLangLib Studio: http://localhost:$STUDIO_PORT"
cd web && npx vite --port "$STUDIO_PORT" --strictPort --clearScreen false
