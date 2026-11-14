// Edit mode: right-click anything that names part of the model (a character,
// a fact, a bond, an event, a paragraph, in the prose or the side panel) to
// inspect it, adjust it directly (story.json, checked by langlib before it is
// written), or ask the listening agent to change it.
import React, { useEffect, useState } from 'react'
import type { Report, State } from './types'
import { charColour, charName } from './Logic'

export interface Vocab { traits: string[]; values: string[]; dims: string[]; bondMax: number }
export interface MenuItem { label: string; run: () => void; sep?: boolean; dim?: boolean }
export interface Menu { x: number; y: number; items: MenuItem[] }

/** Targets under a right-click, innermost first: data-target attributes, then the paragraph. */
export function targetsAt(el: HTMLElement | null): string[] {
  const out: string[] = []
  for (let e = el; e && !e.classList.contains('shell'); e = e.parentElement) {
    for (const t of (e.dataset.target ?? '').split(' ')) if (t && !out.includes(t)) out.push(t)
    if (e.dataset.paraName && !out.includes(`para:${e.dataset.paraName}`)) out.push(`para:${e.dataset.paraName}`)
  }
  return out
}

export function describeTarget(report: Report, t: string): string {
  const [kind, key, idx] = t.split(':')
  if (kind === 'char') return charName(report, key)
  if (kind === 'fact') return `“${report.atoms.find(a => a.id === key)?.label ?? key}”`
  if (kind === 'bond') { const [a, b] = key.split('>'); return `${charName(report, a)} → ${charName(report, b)}` }
  if (kind === 'ev') return `event “${report.paragraphs.find(p => p.name === key)?.events[Number(idx)]?.gloss ?? key}”`
  if (kind === 'para') return `¶ ${key}`
  return key ?? t
}

export function ContextMenu({ menu, onClose }: { menu: Menu; onClose: () => void }) {
  useEffect(() => {
    const close = () => onClose()
    const key = (e: KeyboardEvent) => { if (e.key === 'Escape') onClose() }
    window.addEventListener('mousedown', close)
    window.addEventListener('blur', close)
    window.addEventListener('keydown', key)
    return () => { window.removeEventListener('mousedown', close); window.removeEventListener('blur', close); window.removeEventListener('keydown', key) }
  }, [onClose])
  const w = 280, h = menu.items.length * 28 + 12
  return (
    <ul className="ctx" role="menu" style={{ left: Math.max(8, Math.min(menu.x, innerWidth - w - 8)), top: Math.max(8, Math.min(menu.y, innerHeight - h - 8)) }}
      onMouseDown={e => e.stopPropagation()}>
      {menu.items.map((it, i) => it.sep ? <li key={i} className="ctx-sep" role="separator" /> :
        <li key={i} role="menuitem" className={it.dim ? 'dim' : ''} onClick={() => { it.run(); onClose() }}>{it.label}</li>)}
    </ul>
  )
}

function stateAt(report: Report, current: number): State {
  return report.paragraphs[current]?.state ?? report.start
}

async function save(story: string, target: string, changes: Record<string, unknown>) {
  const r = await fetch(`/api/story/${story}/edit`, {
    method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ target, changes }),
  })
  const body = await r.json()
  if (!r.ok) throw new Error(body.detail ?? r.statusText)
  return body as { changed: string[] }
}

function useSaver(story: string, target: string) {
  const [msg, setMsg] = useState<{ ok: boolean; text: string } | null>(null)
  const [busy, setBusy] = useState(false)
  useEffect(() => setMsg(null), [target])
  const run = async (changes: Record<string, unknown>) => {
    setBusy(true); setMsg(null)
    try {
      const r = await save(story, target, changes)
      setMsg({ ok: true, text: r.changed.length ? `saved: ${r.changed.join('; ')}` : 'nothing changed' })
    } catch (e) { setMsg({ ok: false, text: String((e as Error).message ?? e) }) }
    setBusy(false)
  }
  return { msg, busy, run }
}

function Chips({ all, chosen, ordered, onChange }: {
  all: string[]; chosen: string[]; ordered?: boolean; onChange: (xs: string[]) => void
}) {
  const move = (i: number, d: number) => { const xs = [...chosen]; [xs[i], xs[i + d]] = [xs[i + d], xs[i]]; onChange(xs) }
  return <div className="ins-chips">
    {chosen.map((x, i) => <span key={x} className="chip on">
      {ordered && <b className="dim">{i + 1}.</b>} {x}
      {ordered && i > 0 && <button title="rank higher" onClick={() => move(i, -1)}>↑</button>}
      <button title="remove" onClick={() => onChange(chosen.filter(y => y !== x))}>×</button></span>)}
    {all.filter(x => !chosen.includes(x)).map(x => <button key={x} className="chip add" onClick={() => onChange([...chosen, x])}>+ {x}</button>)}
  </div>
}

function Footer({ saver, dirty, onSave, onAsk }: {
  saver: ReturnType<typeof useSaver>; dirty: boolean; onSave: () => void; onAsk: () => void
}) {
  return <div className="ins-foot">
    <button className="btn primary" disabled={!dirty || saver.busy} onClick={onSave}>{saver.busy ? 'Checking…' : 'Save to the model'}</button>
    <button className="btn" onClick={onAsk}>Ask the agent…</button>
    {saver.msg && <div className={saver.msg.ok ? 'ok' : 'bad'}>{saver.msg.text}</div>}
    <div className="dim">Saving rewrites story.json after langlib has read it; paragraphs re-check live. Prose is not touched.</div>
  </div>
}

function CharInspector({ report, id, current, vocab, onAsk }: {
  report: Report; id: string; current: number; vocab: Vocab; onAsk: () => void
}) {
  const c = report.characters.find(x => x.id === id)!
  const start = report.start
  const startKnows = start.views[id]?.map(l => (l.true ? '' : '!') + l.lit).filter(l => !l.includes('(')) ?? []
  const [traits, setTraits] = useState(c.traits)
  const [values, setValues] = useState(c.values)
  const [pron, setPron] = useState(c.pron)
  const [place, setPlace] = useState(report.startLine[id]?.known ? report.startLine[id].place : '')
  useEffect(() => { setTraits(c.traits); setValues(c.values); setPron(c.pron); setPlace(report.startLine[id]?.known ? report.startLine[id].place : '') }, [report, id])
  const saver = useSaver(report.name, `char:${id}`)
  const dirty = traits.join() !== c.traits.join() || values.join() !== c.values.join() || pron !== c.pron ||
    place !== (report.startLine[id]?.known ? report.startLine[id].place : '')
  const now = stateAt(report, current)
  const where = now.at[id]
  return <div className="inspector">
    <h3><span style={{ color: charColour(report, id) }}>{c.name}</span> <span className="dim">character · {id}</span></h3>
    <section><h4>Persona</h4>
      <div className="ins-row"><span className="k">pronouns</span>
        <select value={pron} onChange={e => setPron(e.target.value)}>{['she', 'he', 'they', 'it'].map(p => <option key={p}>{p}</option>)}</select></div>
      <div className="ins-row"><span className="k">traits</span><Chips all={vocab.traits} chosen={traits} onChange={setTraits} /></div>
      <div className="ins-row"><span className="k">values, ranked</span><Chips all={vocab.values} chosen={values} ordered onChange={setValues} /></div>
      <div className="ins-row"><span className="k">starts at</span>
        <select value={place} onChange={e => setPlace(e.target.value)}>
          <option value="">offstage</option>{report.places.map(p => <option key={p}>{p}</option>)}</select></div>
      <div className="ins-row"><span className="k">knows at the start</span><span>{startKnows.join(', ') || '—'}</span></div>
    </section>
    <Footer saver={saver} dirty={dirty} onAsk={onAsk}
      onSave={() => saver.run({ traits, values, pron, start_place: place })} />
    <section><h4>After ¶ {report.paragraphs[current]?.name ?? 'start'}</h4>
      <div className="ins-row"><span className="k">where</span><span>{where?.known ? where.place : 'unknown / offstage'}</span></div>
      <div className="ins-row"><span className="k">believes</span><ul className="ins-list">{(now.views[id] ?? []).map((l, i) =>
        <li key={i} data-target={l.lit.includes('(') ? '' : `fact:${l.lit.replace(/^!/, '')}`}>{l.gloss}{!l.true && <span className="fb">false</span>}</li>)}</ul></div>
      <div className="ins-row"><span className="k">wants</span><span>{(now.goals[id] ?? []).join(', ') || '—'}</span></div>
      <div className="ins-row"><span className="k">plans</span><span>{(now.plans[id] ?? []).map(p => `${p.goal} (next: ${p.next.join(', ') || 'done'})`).join('; ') || '—'}</span></div>
      <div className="ins-row"><span className="k">bonds</span><div className="chips">{Object.entries(now.bonds).filter(([k]) => k.split('>').includes(id)).map(([k, v]) =>
        <span key={k} className="chip" data-target={`bond:${k}`}>{k.split('>').map(x => charName(report, x)).join(' → ')}: {Object.entries(v).filter(([, n]) => n).map(([d, n]) => `${d} ${n}`).join(', ') || 'none'}</span>)}</div></div>
    </section>
  </div>
}

function FactInspector({ report, id, current, onAsk }: { report: Report; id: string; current: number; onAsk: () => void }) {
  const a = report.atoms.find(x => x.id === id)!
  const [label, setLabel] = useState(a.label)
  const [truth, setTruth] = useState(a.truth)
  useEffect(() => { setLabel(a.label); setTruth(a.truth) }, [report, id])
  const saver = useSaver(report.name, `fact:${id}`)
  const now = stateAt(report, current)
  return <div className="inspector">
    <h3>{a.label} <span className="dim">fact · {id}</span></h3>
    <section><h4>In the story world</h4>
      <div className="ins-row"><span className="k">label</span><input value={label} onChange={e => setLabel(e.target.value)} /></div>
      <div className="ins-row"><span className="k">true?</span>
        <span className="seg"><button className={truth ? 'on' : ''} onClick={() => setTruth(true)}>true</button><button className={!truth ? 'on' : ''} onClick={() => setTruth(false)}>false</button></span></div>
    </section>
    <Footer saver={saver} dirty={label !== a.label || truth !== a.truth} onAsk={onAsk} onSave={() => saver.run({ label, truth })} />
    <section><h4>Who believes it, after ¶ {report.paragraphs[current]?.name ?? 'start'}</h4>
      {report.characters.map(c => {
        const vs = now.views[c.id] ?? []
        const yes = vs.some(l => l.lit === id), no = vs.some(l => l.lit === `!${id}`)
        return <div key={c.id} className="ins-row" data-target={`char:${c.id}`}><span className="k" style={{ color: charColour(report, c.id) }}>{c.name}</span>
          <span className={(yes && !a.truth) || (no && a.truth) ? 'bad' : ''}>{yes ? 'believes it' : no ? 'believes it is false' : 'no view'}{(yes && !a.truth) || (no && a.truth) ? ' (wrong)' : ''}</span></div>
      })}
    </section>
  </div>
}

function BondInspector({ report, pair, current, vocab, onAsk }: { report: Report; pair: string; current: number; vocab: Vocab; onAsk: () => void }) {
  const [a, b] = pair.split('>')
  const init = () => Object.fromEntries(vocab.dims.map(d => [d, report.start.bonds[pair]?.[d] ?? 0]))
  const [v, setV] = useState<Record<string, number>>(init)
  useEffect(() => setV(init()), [report, pair])
  const saver = useSaver(report.name, `bond:${pair}`)
  const dirty = vocab.dims.some(d => v[d] !== (report.start.bonds[pair]?.[d] ?? 0))
  const now = stateAt(report, current).bonds[pair] ?? {}
  return <div className="inspector">
    <h3><span style={{ color: charColour(report, a) }}>{charName(report, a)}</span> → <span style={{ color: charColour(report, b) }}>{charName(report, b)}</span> <span className="dim">bond</span></h3>
    <section><h4>At the start (0 none … {vocab.bondMax} strong)</h4>
      {vocab.dims.map(d => <div key={d} className="ins-row"><span className="k">{d}</span>
        <span className="stepper"><button onClick={() => setV({ ...v, [d]: Math.max(0, v[d] - 1) })}>−</button><b>{v[d]}</b>
          <button onClick={() => setV({ ...v, [d]: Math.min(vocab.bondMax, v[d] + 1) })}>+</button></span>
        <span className="dim">after ¶ {report.paragraphs[current]?.name ?? 'start'}: {now[d] ?? 0}</span></div>)}
    </section>
    <Footer saver={saver} dirty={dirty} onAsk={onAsk} onSave={() => saver.run(v)} />
  </div>
}

function EventInspector({ report, para, i, onAsk }: { report: Report; para: string; i: number; onAsk: () => void }) {
  const p = report.paragraphs.find(x => x.name === para)
  const e = p?.events[i]
  if (!p || !e) return <div className="inspector dim">That event is gone (the reading changed).</div>
  return <div className="inspector">
    <h3>{e.gloss} <span className="dim">event · ¶ {para}</span></h3>
    <section>
      <div className="ins-row"><span className="k">reading</span><code>{e.e}</code></div>
      <div className="ins-row"><span className="k">possible?</span><span className={e.status === 'yes' ? 'ok' : e.status === 'no' ? 'bad' : 'warn'}>{e.status}{e.why ? `: ${e.why}` : ''}</span></div>
      <div className="ins-row"><span className="k">motive</span><span className={e.unmotivated ? 'warn' : ''}>{e.unmotivated ? 'none on the page' : e.motive || '—'}</span></div>
      <div className="ins-row"><span className="k">when</span><span>{e.phase}{e.time ? `, minutes ${e.time[0]}–${e.time[1]}` : ''}</span></div>
      <div className="ins-row"><span className="k">read from</span><span>{e.src === 'text' ? 'the prose' : e.src}{p.freshness?.status === 'stale' ? <span className="bad"> (stale: the prose changed since)</span> : null}</span></div>
    </section>
    <div className="ins-foot">
      <button className="btn" onClick={onAsk}>Ask the agent…</button>
      <div className="dim">Events are read off the prose, so they change through the prose (or a re-reading), not here.</div>
    </div>
  </div>
}

export function InspectorView({ report, target, current, vocab, onAsk }: {
  report: Report; target: string | null; current: number; vocab: Vocab | null; onAsk: (target: string) => void
}) {
  if (!target) return <div className="storyview dim">Right-click a character, fact, bond or event (in the prose or this panel) and choose Inspect.</div>
  if (!vocab) return <div className="storyview dim">Loading…</div>
  const [kind, key, idx] = target.split(':')
  const ask = () => onAsk(target)
  if (kind === 'char' && report.characters.some(c => c.id === key)) return <CharInspector report={report} id={key} current={current} vocab={vocab} onAsk={ask} />
  if (kind === 'fact' && report.atoms.some(a => a.id === key)) return <FactInspector report={report} id={key} current={current} onAsk={ask} />
  if (kind === 'bond') return <BondInspector report={report} pair={key} current={current} vocab={vocab} onAsk={ask} />
  if (kind === 'ev') return <EventInspector report={report} para={key} i={Number(idx)} onAsk={ask} />
  return <div className="storyview dim">{describeTarget(report, target)}: nothing to inspect here yet; you can still ask the agent.
    <div><button className="btn small" onClick={ask}>Ask the agent…</button></div></div>
}
