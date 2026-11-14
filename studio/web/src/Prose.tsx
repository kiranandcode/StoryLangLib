import React, { useMemo } from 'react'
import type { Paragraph, Report, Token, EventRow } from './types'

export interface Hover { x: number; y: number; body: React.ReactNode }

/** The colour of an entity: its character's, or neutral. */
export function entityColour(report: Report, ent: string | undefined, docEnts?: { id: string; name: string }[]): string {
  if (!ent) return 'var(--ink-3)'
  const name = docEnts?.find(e => e.id === ent)?.name.toLowerCase()
  const i = report.characters.findIndex(c =>
    c.id === ent.toLowerCase() || c.name.toLowerCase() === ent.toLowerCase() || (name && c.name.toLowerCase() === name))
  return i >= 0 ? `var(--c${i % 6})` : 'var(--ink-3)'
}

/** Character offsets of each token in the source text (tokens are substrings, in order). */
function align(text: string, toks: Token[]): { start: number; end: number }[] {
  const out: { start: number; end: number }[] = []
  let at = 0
  for (const t of toks) {
    const i = text.indexOf(t.w, at)
    if (i < 0) { out.push({ start: at, end: at }); continue }
    out.push({ start: i, end: i + t.w.length })
    at = i + t.w.length
  }
  return out
}

export function warningsOf(p: Paragraph): { cls: string; glyph: string; text: string }[] {
  const out: { cls: string; glyph: string; text: string }[] = []
  for (const e of p.events) {
    if (e.status === 'no') {
      const ooc = e.why.startsWith('out of character')
      const leak = e.why.includes('no way to know') || e.why.includes('says they know it')
      out.push({ cls: 'bad', glyph: ooc ? '↯' : leak ? '⊘' : '✕', text: `${e.gloss}: ${e.why}` })
    } else if (e.status === 'unknown') {
      out.push({ cls: 'warn', glyph: '◐', text: `assumed: ${e.gloss} (${e.why})` })
    }
    if (e.unmotivated) out.push({ cls: 'warn', glyph: '?', text: `unmotivated: ${e.gloss} (${e.motive})` })
  }
  for (const c of p.claims) if (!c.holds) out.push({ cls: 'bad', glyph: '≠', text: `claim does not hold: ${c.claim}${c.error ? ` (${c.error})` : ''}` })
  if (p.realisation && !p.realisation.realises)
    out.push({ cls: 'bad', glyph: '⇎', text: `prose does not realise the plan: missing ${p.realisation.missing.join(', ') || 'none'}; extra ${p.realisation.extra.join(', ') || 'none'}` })
  if (p.doc && !p.doc.check.ok) out.push({ cls: 'bad', glyph: '¶', text: `annotation rejected: ${[...p.doc.check.edits, ...p.doc.check.refIssues].slice(0, 3).join('; ')}` })
  for (const e of p.errors) out.push({ cls: 'bad', glyph: '!', text: e })
  return out
}

interface ParaProps {
  report: Report
  p: Paragraph
  index: number
  overview: boolean
  current: boolean
  hoverEnt: string | null
  setHoverEnt: (e: string | null) => void
  setHover: (h: Hover | null) => void
  onRequest?: (index: number) => void
  requests?: number
  onSelect: (i: number) => void
}

export const ParagraphView = React.memo(function ParagraphView(props: ParaProps) {
  const { report, p, index, overview, current, hoverEnt, setHoverEnt, setHover, onSelect, onRequest, requests } = props
  const doc = p.doc
  const evAt = useMemo(() => {
    const m = new Map<number, { e: string; gloss?: string; status?: string; why?: string; lex?: boolean }[]>()
    for (const e of p.events) if (e.at !== null) {
      m.set(e.at, [...(m.get(e.at) ?? []), { e: e.e, gloss: e.gloss, status: e.status, why: e.why }])
    }
    for (const l of p.lexicon) if (!p.events.some(e => e.at === l.at && e.e === l.e))
      m.set(l.at, [...(m.get(l.at) ?? []), { e: l.e, lex: true, status: l.asserted ? 'yes' : 'lexicon only' }])
    return m
  }, [p])
  const warn = warningsOf(p)
  const speakers = doc ? [...new Set(doc.tokens.map(t => t.spk).filter((s): s is string => !!s && s !== '?'))] : []

  const body = useMemo(() => {
    if (!p.text.trim()) return null
    if (!doc || !doc.tokens.length) return p.text.trim()
    const spans = align(p.text, doc.tokens)
    const out: React.ReactNode[] = []
    let at = 0
    doc.tokens.forEach((t, i) => {
      const { start, end } = spans[i]
      if (start > at) out.push(p.text.slice(at, start).replace(/\s+/g, ' '))
      const cls = ['tok', `p-${t.p}`]
      const style: Record<string, string> = {}
      if (t.ent) {
        cls.push('ent', t.mk === 'pron' ? 'pron' : 'name')
        if (t.phora === 'cataphoric') cls.push('cataphoric')
        if (hoverEnt && t.ent === hoverEnt) cls.push('hl')
        style['--ec'] = entityColour(report, t.ent, doc.entities)
      }
      if (t.spk) { cls.push('quote'); style['--qc'] = entityColour(report, t.spk, doc.entities) }
      if (t.time) cls.push('time')
      const tg: string[] = []
      if (t.ent) tg.push(report.characters.some(c => c.id === t.ent) ? `char:${t.ent}` : report.places.includes(t.ent) ? `place:${t.ent}` : report.objects.includes(t.ent) ? `obj:${t.ent}` : '')
      p.events.forEach((e, k) => { if (e.at === i) tg.push(`ev:${p.name}:${k}`) })
      const evs = evAt.get(i)
      if (evs) {
        cls.push('ev')
        const worst = evs.some(e => e.status === 'no') ? 'no' : evs.some(e => e.status === 'unknown') ? 'unknown' : 'yes'
        cls.push(worst)
      }
      out.push(<span key={i} className={cls.join(' ')} style={style as React.CSSProperties} data-i={i} data-target={tg.filter(Boolean).join(' ') || undefined}>{p.text.slice(start, end)}</span>)
      at = end
    })
    if (at < p.text.length) out.push(p.text.slice(at).replace(/\s+$/, ''))
    return out
  }, [p, doc, evAt, hoverEnt, report])

  const onOver = (ev: React.MouseEvent) => {
    if (!overview || !doc) return
    const el = (ev.target as HTMLElement).closest('[data-i]') as HTMLElement | null
    if (!el) { setHover(null); setHoverEnt(null); return }
    const i = Number(el.dataset.i)
    const t = doc.tokens[i]
    const rows: React.ReactNode[] = []
    if (t.ent) {
      const ent = doc.entities.find(e => e.id === t.ent)
      rows.push(<div key="ent" className="row"><span className="k">{t.mk === 'pron' ? 'pronoun' : 'mention'}</span> {ent?.name ?? t.ent}{t.phora && t.phora !== 'full' ? ` · ${t.phora}` : ''}</div>)
      setHoverEnt(t.ent)
    } else setHoverEnt(null)
    rows.push(<div key="pos" className="row"><span className="k">pos</span> <code>{t.p}</code></div>)
    if (t.spk) rows.push(<div key="spk" className="row"><span className="k">speaker</span> {doc.entities.find(e => e.id === t.spk)?.name ?? t.spk}</div>)
    const evs = evAt.get(i)
    if (evs) for (const e of evs) rows.push(
      <div key={e.e} className="row"><span className="k">{e.lex ? 'read by the lexicon' : 'event'}</span> {e.gloss ?? e.e}<br /><code>{e.e}</code>{e.status && e.status !== 'yes' ? <> · <b>{e.status}</b></> : null}{e.why ? <div>{e.why}</div> : null}</div>)
    if (t.time) rows.push(<div key="time" className="row"><span className="k">time word</span></div>)
    const r = el.getBoundingClientRect()
    setHover({ x: r.left, y: r.bottom + 6, body: rows })
  }

  const cls = ['para']
  if (index === 0) cls.push('first')
  if (current) cls.push('current')
  if (!p.text.trim()) cls.push('empty')
  return (
    <p className={cls.join(' ')} data-para={index} data-para-name={p.name} onMouseOver={onOver}
       onMouseLeave={() => { setHover(null); setHoverEnt(null) }}>
      {overview && (
        <span className="gutter">
          <span className="num" onClick={() => onSelect(index)} title={`paragraph ${p.name}`}>{p.name}</span>
          {speakers.length > 0 && <span className="spk">{speakers.map(s =>
            <i key={s} style={{ color: entityColour(report, s, doc?.entities) }} title={`speaks: ${s}`}>{(doc?.entities.find(e => e.id === s)?.name ?? s)[0]?.toUpperCase()}</i>)}</span>}
          {warn.slice(0, 4).map((w, i) => (
            <span key={i} className={`mark ${w.cls}`}
              onMouseEnter={e => { const r = (e.target as HTMLElement).getBoundingClientRect(); setHover({ x: r.right + 8, y: r.top, body: <div>{w.text}</div> }) }}
              onMouseLeave={() => setHover(null)}>{w.glyph}</span>))}
          {p.freshness?.status === 'stale' && <span className="mark bad" title={`reading is stale: ${p.freshness.why.join('; ')}`}>⟳</span>}
          {warn.length === 0 && p.text.trim() && <span className="mark ok" title={p.verdict}>·</span>}
          {onRequest && requests ? <span className={`mark req-mark ${requests ? 'has' : ''}`} onMouseDown={e => e.preventDefault()} onClick={() => onRequest(index)}
            title={requests ? `${requests} open request${requests > 1 ? 's' : ''} on this paragraph; click to add another` : 'request a change to this paragraph (select text first to quote it)'}>
            {`✎${requests}`}</span> : null}
        </span>
      )}
      {body ?? <span>({p.events.length} planned events, no prose yet: {p.events.map(e => e.gloss).join('; ')})</span>}
    </p>
  )
})

export function eventLabel(e: EventRow) { return e.gloss }
