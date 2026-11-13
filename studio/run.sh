#!/usr/bin/env bash
# StoryLangLib Studio: one command. Backend (FastAPI, reloads on Python edits;
# watches stories/ and pushes updates) + frontend (Vite, hot module reload).
#   studio/run.sh            ports: UI 5177, API 8765 (STUDIO_PORT, STUDIO_API_PORT)
# Ctrl-C or a TERM stops both; uvicorn's shutdown kills the Lean/langlib
# process groups it started (studio/procs.py).
set -euo pipefail
cd "$(dirname "$0")"
ROOT="$(cd .. && pwd)"
export STUDIO_PORT="${STUDIO_PORT:-5177}" STUDIO_API_PORT="${STUDIO_API_PORT:-8765}"

[ -x "$ROOT/.lake/build/bin/langlib" ] || (cd "$ROOT" && nice -n 10 lake build)
if [ ! -x .venv/bin/uvicorn ]; then
  uv venv -q .venv && uv pip install -q --python .venv/bin/python fastapi "uvicorn[standard]" watchfiles
fi
[ -d web/node_modules ] || (cd web && npm install --silent)

.venv/bin/uvicorn server:app --reload --reload-exclude 'workflows.py' --reload-exclude '.pgids' --reload-exclude 'web/*' --reload-exclude '.venv/*' --timeout-graceful-shutdown 1 --port "$STUDIO_API_PORT" --log-level warning &
API=$!
(cd web && exec npx vite --port "$STUDIO_PORT" --strictPort --clearScreen false) &
WEB=$!
# children run in the background so a signal to this script is handled at once
stop() { trap - EXIT INT TERM HUP; kill -TERM "$API" 2>/dev/null; pkill -TERM -P "$WEB" 2>/dev/null; kill -TERM "$WEB" 2>/dev/null; wait; }
trap stop EXIT INT TERM HUP
echo "StoryLangLib Studio: http://localhost:$STUDIO_PORT"
wait
