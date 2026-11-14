// Runs Electron and restarts it when electron/*.cjs changes. Exits (with
// Electron's code) when the app quits on its own, so the launcher can stop
// the rest; TERM/INT/HUP stop Electron and then exit.
const { spawn } = require('child_process')
const fs = require('fs')
const path = require('path')
const electron = require('electron')

const dir = __dirname
let child = null, restarting = false, stopping = false, timer = null

function start() {
  child = spawn(electron, [path.join(dir, 'main.cjs')], { stdio: 'inherit', env: process.env })
  child.on('exit', (code, sig) => {
    if (restarting) { restarting = false; start(); return }
    process.exit(stopping ? 0 : code ?? (sig ? 1 : 0))
  })
}

function stop(sig) {
  stopping = true
  if (!child || child.exitCode !== null) process.exit(0)
  child.kill(sig)
  setTimeout(() => { try { child.kill('SIGKILL') } catch {} process.exit(0) }, 3000).unref()
}

fs.watch(dir, (_, f) => {
  if (!f || !f.endsWith('.cjs') || f === 'dev.cjs') return
  clearTimeout(timer)
  timer = setTimeout(() => {
    console.log(`[electron] ${f} changed: restarting the main process`)
    restarting = true
    child.kill('SIGTERM')
  }, 200)
})
for (const s of ['SIGTERM', 'SIGINT', 'SIGHUP']) process.on(s, () => stop('SIGTERM'))
start()
