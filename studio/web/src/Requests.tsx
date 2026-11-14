// Kiran's requests: a composer (top bar, ✎ in a paragraph's gutter, or `r`)
// and the list with the agent's replies. Requests go to studio/requests.jsonl;
// an interactive agent listening through studio/studio_mcp.py picks them up.
import React, { useEffect, useRef, useState } from 'react'
import type { StudioRequest } from './types'

export interface Draft { kind: 'story' | 'tool'; para: string; quote: string }

const LABEL: Record<string, string> = {
  open: 'waiting', claimed: 'picked up', working: 'working', done: 'done', declined: 'declined',
}

function ago(t: number) {
  const s = Date.now() / 1000 - t
  return s < 60 ? 'just now' : s < 3600 ? `${Math.round(s / 60)} min ago` : s < 86400 ? `${Math.round(s / 3600)} h ago` : new Date(t * 1000).toLocaleDateString()
}

export function Composer({ story, draft, onClose, onSent }: {
  story: string; draft: Draft; onClose: () => void; onSent: () => void
}) {
  const [kind, setKind] = useState(draft.kind)
  const [text, setText] = useState('')
  const [quote, setQuote] = useState(draft.quote)
  const [err, setErr] = useState('')
  const [busy, setBusy] = useState(false)
  const ta = useRef<HTMLTextAreaElement>(null)
  useEffect(() => { ta.current?.focus() }, [])

  const send = async () => {
    if (!text.trim() || busy) return
    setBusy(true); setErr('')
    try {
      const r = await fetch('/api/requests', {
        method: 'POST', headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ kind, text, story: kind === 'story' ? story : '', para: kind === 'story' ? draft.para : '', quote }),
      })
      if (!r.ok) throw new Error((await r.json()).detail ?? r.statusText)
      onSent(); onClose()
    } catch (e) { setErr(String(e)); setBusy(false) }
  }

  return (
    <div className="modal-back" onMouseDown={e => { if (e.target === e.currentTarget) onClose() }}>
      <div className="composer" role="dialog" aria-label="request a change"
        onKeyDown={e => { if (e.key === 'Escape') onClose(); if (e.key === 'Enter' && (e.metaKey || e.ctrlKey)) send() }}>
        <div className="composer-head">
          <span className="seg" role="group" aria-label="what to change">
            <button className={kind === 'story' ? 'on' : ''} onClick={() => setKind('story')}>Story</button>
            <button className={kind === 'tool' ? 'on' : ''} onClick={() => setKind('tool')}>Tool</button>
          </span>
          <span className="dim">{kind === 'story' ? (draft.para ? `paragraph ${draft.para}` : 'the whole story') : 'the Studio or langlib'}</span>
        </div>
        {kind === 'story' && quote && <blockquote className="req-quote">“{quote}” <button className="btn small" onClick={() => setQuote('')}>drop quote</button></blockquote>}
        <textarea ref={ta} value={text} onChange={e => setText(e.target.value)} rows={5}
          placeholder={kind === 'story' ? 'What should change? e.g. “Theo is too smooth here; make him nervous.”' : 'What should the tool do differently?'} />
        {err && <div className="err">{err}</div>}
        <div className="composer-foot">
          <span className="dim">An agent listening in a termling picks this up. ⌘↵ to send, Esc to cancel.</span>
          <span className="spacer" />
          <button className="btn" onClick={onClose}>Cancel</button>
          <button className="btn primary" disabled={!text.trim() || busy} onClick={send}>Send</button>
        </div>
      </div>
    </div>
  )
}

export function RequestsView({ requests, story, onNew, onSelectPara }: {
  requests: StudioRequest[]; story: string; onNew: () => void; onSelectPara: (name: string) => void
}) {
  const mine = requests.filter(r => r.kind === 'tool' || r.story === story).slice().reverse()
  const withdraw = (id: string) => fetch(`/api/requests/${id}/withdraw`, { method: 'POST' })
  return (
    <div className="storyview requests">
      <section>
        <h3>Requests <button className="btn small" onClick={onNew}>new (r)</button></h3>
        {mine.length === 0 && <div className="dim">Nothing asked yet. Select some prose and press ✎ in its margin, or use “Request” in the top bar.</div>}
        <ul className="reqs">{mine.map(r => (
          <li key={r.id} className={`req st-${r.status}`}>
            <div className="req-head">
              <span className={`badge req-${r.status}`}>{LABEL[r.status] ?? r.status}</span>
              <span className="dim">{r.kind === 'tool' ? 'tool' : r.para ? <a onClick={() => onSelectPara(r.para)}>¶ {r.para}</a> : 'story'} · {ago(r.at)}</span>
              <span className="spacer" />
              {(r.status === 'open') && <button className="btn small" onClick={() => withdraw(r.id)}>withdraw</button>}
            </div>
            {r.quote && <blockquote className="req-quote">“{r.quote}”</blockquote>}
            <div className="req-text">{r.text}</div>
            {r.reply && <div className="req-reply">{r.reply}</div>}
          </li>))}
        </ul>
      </section>
    </div>
  )
}
