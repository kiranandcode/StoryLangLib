#!/usr/bin/env bash
# StoryLangLib Studio: one command. Backend (FastAPI, reloads on Python edits;
# watches stories/ and pushes updates) + frontend (Vite, hot module reload).
# The Electron window loads the Vite dev server; the same URL works in a browser.
#   studio/run.sh            API, Vite and the Electron app
#   studio/run.sh --browser  API and Vite only (open the URL yourself)
#   ports: UI 5177, API 8765 (STUDIO_PORT, STUDIO_API_PORT)
# Quitting the app, Ctrl-C or a TERM stops everything; uvicorn's shutdown
# kills the Lean/langlib process groups it started (studio/procs.py).
set -euo pipefail
cd "$(dirname "$0")"
ROOT="$(cd .. && pwd)"
ELECTRON=1; [ "${1:-}" = "--browser" ] && ELECTRON=0
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
APP=
if [ "$ELECTRON" = 1 ]; then (cd web && exec node electron/dev.cjs) & APP=$!; fi
# children run in the background so a signal to this script is handled at once
stop() {
  set +e; trap - EXIT INT TERM HUP
  if [ -n "$APP" ]; then kill -TERM "$APP" 2>/dev/null; fi
  kill -TERM "$API" 2>/dev/null; pkill -TERM -P "$WEB" 2>/dev/null; kill -TERM "$WEB" 2>/dev/null
  wait
}
trap stop EXIT INT TERM HUP
echo "StoryLangLib Studio: http://localhost:$STUDIO_PORT"
# stop everything as soon as any part exits (quitting the app, a crash)
while kill -0 "$API" 2>/dev/null && kill -0 "$WEB" 2>/dev/null && { [ -z "$APP" ] || kill -0 "$APP" 2>/dev/null; }; do
  sleep 0.5
done
