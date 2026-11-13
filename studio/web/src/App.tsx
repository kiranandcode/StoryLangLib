import React, { useCallback, useEffect, useRef, useState } from 'react'
import type { Report } from './types'
import { ParagraphView, type Hover, entityColour } from './Prose'
import { LogicPanel } from './Logic'
import { ProofView, RunsView, StoryView } from './StoryViews'

function usePref<T extends string>(key: string, init: T): [T, (v: T) => void] {
  const [v, setV] = useState<T>(() => {
    try { return (localStorage.getItem(key) as T) ?? init } catch { return init }
  })
  const set = (x: T) => { setV(x); try { localStorage.setItem(key, x) } catch { /* private mode */ } }
  return [v, set]
}

type Tab = 'paragraphs' | 'story' | 'proofs' | 'runs'

export function App() {
  const [stories, setStories] = useState<{ name: string; title: string }[]>([])
  const [story, setStory] = usePref<string>('studio.story', '')
  const [report, setReport] = useState<Report | null>(null)
  const [theme, setTheme] = usePref<'light' | 'dark'>('studio.theme',
    document.documentElement.dataset.theme === 'dark' ? 'dark' : 'light')
  const [mode, setMode] = usePref<'chill' | 'overview'>('studio.mode', 'overview')
  const [pos, setPos] = usePref<'on' | 'off'>('studio.pos', 'off')
  const [face, setFace] = usePref<'serif' | 'sans'>('studio.face', 'serif')
  const [size, setSize] = usePref<string>('studio.size', '20')
  const [tab, setTab] = useState<Tab>('paragraphs')
  const [current, setCurrent] = useState(0)
  const [hover, setHover] = useState<Hover | null>(null)
  const [hoverEnt, setHoverEnt] = useState<string | null>(null)
  const [live, setLive] = useState(false)
  const [flash, setFlash] = useState(0)
  const proseRef = useRef<HTMLDivElement>(null)
  const logicRef = useRef<HTMLDivElement>(null)
  const fromProse = useRef(false)

  useEffect(() => { document.documentElement.dataset.theme = theme }, [theme])

  const load = useCallback((name: string) => {
    if (!name) return
    fetch(`/api/story/${name}`).then(r => r.json()).then((r: Report) => { setReport(r); setFlash(x => x + 1) }).catch(() => {})
  }, [])

  useEffect(() => {
    fetch('/api/stories').then(r => r.json()).then((s: { name: string; title: string }[]) => {
      setStories(s)
      if (s.length && !s.some(x => x.name === story)) setStory(s[0].name)
    }).catch(() => {})
  }, [])
  useEffect(() => { load(story) }, [story, load])

  // live: the server pushes an event whenever the story's files change
  useEffect(() => {
    const es = new EventSource('/api/events')
    es.onopen = () => setLive(true)
    es.onerror = () => setLive(false)
    es.onmessage = m => {
      const msg = JSON.parse(m.data)
      if (msg.story !== story) return
      if (msg.type === 'story') load(story)
      if (msg.type === 'proofs') setReport(r => r ? { ...r, proofs: msg.proofs } : r)
    }
    return () => es.close()
  }, [story, load])

  // the paragraph at the reading line (40% down) is current
  useEffect(() => {
    const pane = proseRef.current
    if (!pane) return
    const onScroll = () => {
      const line = pane.getBoundingClientRect().top + pane.clientHeight * 0.4
      const paras = [...pane.querySelectorAll<HTMLElement>('[data-para]')]
      let best = 0
      for (const p of paras) if (p.getBoundingClientRect().top <= line) best = Number(p.dataset.para)
      setCurrent(c => { if (c !== best) fromProse.current = true; return best })
    }
    pane.addEventListener('scroll', onScroll, { passive: true })
    onScroll()
    return () => pane.removeEventListener('scroll', onScroll)
  }, [report, mode])

  // follow the prose on the right
  useEffect(() => {
    if (!fromProse.current) return
    fromProse.current = false
    const card = logicRef.current?.querySelector<HTMLElement>(`[data-card="${current}"]`)
    const panel = logicRef.current
    if (card && panel) {
      const reduce = matchMedia('(prefers-reduced-motion: reduce)').matches
      panel.scrollTo({ top: card.offsetTop - 12, behavior: reduce ? 'auto' : 'smooth' })
    }
  }, [current])

  const select = useCallback((i: number) => {
    setCurrent(i)
    const el = proseRef.current?.querySelector<HTMLElement>(`[data-para="${i}"]`)
    const pane = proseRef.current
    if (el && pane) pane.scrollTo({ top: el.offsetTop - pane.clientHeight * 0.3, behavior: 'smooth' })
  }, [])

  // keyboard: d theme, o overview, j/k paragraphs
  useEffect(() => {
    const onKey = (e: KeyboardEvent) => {
      if ((e.target as HTMLElement).tagName === 'SELECT' || e.metaKey || e.ctrlKey) return
      if (e.key === 'd') setTheme(theme === 'dark' ? 'light' : 'dark')
      if (e.key === 'o') setMode(mode === 'chill' ? 'overview' : 'chill')
      if (e.key === 'j' && report) select(Math.min(report.paragraphs.length - 1, current + 1))
      if (e.key === 'k') select(Math.max(0, current - 1))
    }
    window.addEventListener('keydown', onKey)
    return () => window.removeEventListener('keydown', onKey)
  })

  const overview = mode === 'overview'
  const proofs = report?.proofs
  const nThm = Object.keys(proofs?.theorems ?? {}).length
  const okThm = Object.values(proofs?.theorems ?? {}).filter(t => t.ok).length

  return (
    <div className="shell">
      <header className="topbar">
        <span className="title">StoryLangLib Studio</span>
        {stories.length > 1 && <select value={story} onChange={e => setStory(e.target.value)}>
          {stories.map(s => <option key={s.name} value={s.name}>{s.title}</option>)}</select>}
        <span className="seg" role="group" aria-label="mode">
          <button className={mode === 'chill' ? 'on' : ''} onClick={() => setMode('chill')} title="just the prose (o)">Chill</button>
          <button className={mode === 'overview' ? 'on' : ''} onClick={() => setMode('overview')} title="annotations and logic (o)">Overview</button>
        </span>
        {overview && <button className={`btn ${pos === 'on' ? 'on' : ''}`} onClick={() => setPos(pos === 'on' ? 'off' : 'on')} title="tint parts of speech">POS</button>}
        <span className="spacer" />
        {report && overview && <span className={`badge ${report.verdict.valid ? 'valid' : report.verdict.plausible ? 'plausible' : 'failing'}`}>
          story {report.verdict.valid ? 'valid' : report.verdict.plausible ? 'plausible' : 'failing'}</span>}
        {report && overview && proofs && <span className={`badge lean ${proofs.status === 'ok' ? 'ok' : proofs.status === 'failed' || proofs.status === 'error' ? 'bad' : ''}`}
          onClick={() => setTab('proofs')} style={{ cursor: 'pointer' }}>
          {proofs.status === 'running' ? 'Lean: checking…' : proofs.status === 'none' ? 'Lean: –' : `Lean ${okThm}/${nThm}`}</span>}
        <button className="btn" onClick={() => setSize(String(Math.max(16, Number(size) - 1)))} title="smaller text">A−</button>
        <button className="btn" onClick={() => setSize(String(Math.min(26, Number(size) + 1)))} title="larger text">A+</button>
        <button className="btn" onClick={() => setFace(face === 'serif' ? 'sans' : 'serif')} title="serif or Atkinson Hyperlegible">{face === 'serif' ? 'Serif' : 'Sans'}</button>
        <button className="btn" onClick={() => setTheme(theme === 'dark' ? 'light' : 'dark')} title="dark or light (d)">{theme === 'dark' ? '☾' : '☀'}</button>
        <span className="live" title={live ? 'following the story files' : 'disconnected'}><span key={flash} className={`dot ${live ? 'on flash' : ''}`} />live</span>
      </header>
      <div className="main">
        <div className="prose-pane" ref={proseRef}>
          {!report && <div className="prose"><p className="para empty">Loading…</p></div>}
          {report?.error && <div className="prose"><p className="para empty">The checker could not read this story: {report.error}</p></div>}
          {report && !report.error && <>
            <article className={`prose ${face === 'sans' ? 'sans' : ''} ${overview ? 'overview' : 'chill'} ${pos === 'on' ? 'pos' : ''} ${hoverEnt ? 'hl' : ''}`}
              style={{ ['--size' as string]: `${size}px` }}>
              <h1>{report.title}</h1>
              <div className="byline">{report.characters.map(c => c.name).join(', ')}</div>
              {report.paragraphs.map((p, i) => (
                <ParagraphView key={p.name} report={report} p={p} index={i} overview={overview}
                  current={overview && i === current} hoverEnt={hoverEnt} setHoverEnt={setHoverEnt}
                  setHover={setHover} onSelect={select} />
              ))}
            </article>
            {overview && <div className="legend">
              {report.characters.map(c => <span key={c.id}><i className="sw" style={{ borderColor: entityColour(report, c.id) }} />{c.name}</span>)}
              <span><i className="sw" style={{ borderBottomStyle: 'dotted', borderColor: 'var(--ink-3)' }} />pronoun</span>
              <span><i className="sw" style={{ borderBottomStyle: 'dashed', borderColor: 'var(--ink-3)', borderBottomWidth: 1 }} />time word</span>
              <span>• event</span><span>◐ assumed</span><span>✕ ruled out</span><span>↯ out of character</span><span>? unmotivated</span>
            </div>}
          </>}
        </div>
        {overview && report && !report.error && (
          <aside className="right">
            <nav className="tabs">
              {(['paragraphs', 'story', 'proofs', 'runs'] as Tab[]).map(t =>
                <button key={t} className={tab === t ? 'on' : ''} onClick={() => setTab(t)}>{t}</button>)}
            </nav>
            {tab === 'paragraphs' && <LogicPanel report={report} current={current} onSelect={select} scrollRef={logicRef} />}
            {tab === 'story' && <div className="logic"><StoryView report={report} current={current} /></div>}
            {tab === 'proofs' && <div className="logic"><ProofView report={report} onProve={() => fetch(`/api/story/${story}/prove`, { method: 'POST' })} /></div>}
            {tab === 'runs' && <div className="logic"><RunsView report={report} /></div>}
          </aside>
        )}
      </div>
      {hover && overview && <div className="card-pop" style={{ left: Math.min(hover.x, innerWidth - 360), top: Math.min(hover.y, innerHeight - 160) }}>{hover.body}</div>}
    </div>
  )
}
