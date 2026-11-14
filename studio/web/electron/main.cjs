// StoryLangLib Studio's Electron shell. In development the window loads the
// Vite dev server (hot module reload for the renderer); electron/dev.cjs
// restarts this process when its files change. Closing the window quits the
// app, and studio/run.sh then stops the API and Vite, whose shutdown reaps
// the Lean/langlib process groups (studio/procs.py).
const { app, BrowserWindow, shell } = require('electron')

const URL = process.env.STUDIO_URL || `http://localhost:${process.env.STUDIO_PORT || 5177}`
if (process.env.STUDIO_CDP_PORT) app.commandLine.appendSwitch('remote-debugging-port', process.env.STUDIO_CDP_PORT)

let win = null

async function loadWhenUp(w) {
  for (let i = 0; i < 120 && !w.isDestroyed(); i++) {
    try { await w.loadURL(URL); return } catch { await new Promise(r => setTimeout(r, 500)) }
  }
}

function open() {
  win = new BrowserWindow({
    width: 1360, height: 900, minWidth: 480, minHeight: 400,
    title: 'StoryLangLib Studio', backgroundColor: '#fbf8f2',
    webPreferences: { contextIsolation: true, sandbox: true, nodeIntegration: false },
  })
  win.webContents.setWindowOpenHandler(({ url }) => { shell.openExternal(url); return { action: 'deny' } })
  win.on('closed', () => { win = null })
  loadWhenUp(win)
}

app.whenReady().then(open)
app.on('window-all-closed', () => app.quit())   // on macOS too: closing the window ends the session
for (const s of ['SIGTERM', 'SIGINT', 'SIGHUP']) process.on(s, () => app.quit())
