import React, { useEffect, useMemo, useState } from 'react'
import type { PMove, PState, PowerExport, Report } from './types'

/** The Power view: any rule-based module (Nen, Magic, Death Note) that emits
 *  studio/power-schema.md. It follows the reading line: the move shown is the
 *  last of the current paragraph, and the scrubber steps through the moves.
 *  For each move, every precondition in words with pass or fail, and what the
 *  move changed; the state after it; resources as sparklines on one scale;
 *  standing effects and time windows as interval lanes; what each mind holds
 *  of the rules, with false beliefs marked; and the runs the module proves
 *  fail, with the check that stops them. docs/ui-visualisation.md §9. */

const KIND_LABEL: Record<string, string> = {
  status: 'status', resource: 'resource', possession: 'possession', body: 'body', position: 'position',
  support: 'support', target: 'target', knowledge: 'knowledge', time: 'time', rule: 'rule',
}

type Names = (id: string) => string

function namesOf(p: PowerExport, report: Report | null): Names {
  const m = new Map(p.actors.map(a => [a.id, a.name]))
  return id => report?.characters.find(c => c.id === id)?.name ?? m.get(id) ?? id
}

const show = (v: unknown): string => Array.isArray(v) ? (v.length ? v.join(', ') : 'none') : String(v)

/** What changed between two states, in words. */
export function diffStates(a: PState, b: PState, name: Names): string[] {
  const out: string[] = []
  for (const [id, y] of Object.entries(b.actors)) {
    const x = a.actors[id]
    if (!x) continue
    for (const [r, n] of Object.entries(y.resources)) {
      const m = x.resources[r] ?? 0
      if (m !== n) out.push(`${name(id)}'s ${r} ${m} → ${n}`)
    }
    for (const f of y.fields) {
      const g = x.fields.find(z => z.key === f.key)
      if (!g) out.push(`${name(id)}: ${f.label} ${show(f.value)}`)
      else if (show(g.value) !== show(f.value)) out.push(`${name(id)}: ${f.label} ${show(g.value)} → ${show(f.value)}`)
    }
    for (const f of x.fields) if (!y.fields.some(z => z.key === f.key)) out.push(`${name(id)}: no longer ${f.label} ${show(f.value)}`)
    const key = (m: { kind: string; by: string; via: string; note: string }) => `${m.kind}|${m.by}|${m.via}|${m.note}`
    for (const m of y.marks) if (!x.marks.some(n => key(n) === key(m))) out.push(`${name(id)} now bears a ${m.kind} (${m.via}, ${name(m.by)})${m.note ? `: ${m.note}` : ''}`)
    for (const m of x.marks) if (!y.marks.some(n => key(n) === key(m)) && !y.marks.some(n => n.kind === m.kind && n.by === m.by && n.via === m.via))
      out.push(`the ${m.kind} on ${name(id)} is gone`)
    for (const s of y.status) if (!x.status.includes(s)) out.push(`${name(id)} is ${s}`)
    for (const s of x.status) if (!y.status.includes(s)) out.push(`${name(id)} is no longer ${s}`)
  }
  const ak = (e: { by: string; what: string }) => `${e.by}|${e.what}`
  for (const e of b.active) if (!a.active.some(x => ak(x) === ak(e))) out.push(`${e.what} (${name(e.by)}) is up`)
  for (const e of a.active) if (!b.active.some(x => ak(x) === ak(e))) out.push(`${e.what} (${name(e.by)}) ends`)
  const rk = (r: { from: string; to: string; kind: string }) => `${r.from}|${r.to}|${r.kind}`
  for (const r of b.relations) if (!a.relations.some(x => rk(x) === rk(r))) out.push(`${name(r.from)} ${r.label} ${name(r.to)}`)
  for (const r of a.relations) if (!b.relations.some(x => rk(x) === rk(r))) out.push(`${name(r.from)} no longer ${r.label} ${name(r.to)}`)
  for (const c of b.clocks) { const o = a.clocks.find(x => x.id === c.id); if (!o) out.push(`clock started: ${c.label} (due at ${c.due} s)`); else if (o.status !== c.status) out.push(`${c.label}: ${c.status}`) }
  const kk = (k: { who: string; what: string }) => `${k.who}|${k.what}`
  for (const k of b.knowledge) if (!a.knowledge.some(x => kk(x) === kk(k))) out.push(`${name(k.who)} now holds: ${k.what}${k.true ? '' : ' (false)'}`)
  return out
}

export function Checks({ checks, all }: { checks: { id: string; kind: string; label: string; pass: boolean; why: string }[]; all?: boolean }) {
  const failing = checks.filter(c => !c.pass)
  const shown = all ? checks : failing.length ? failing : checks
  return <ul className="pchecks">
    {shown.map(c => <li key={c.id} className={c.pass ? 'ok' : 'bad'} data-target={`pcheck:${c.id}`}>
      <span className="st">{c.pass ? '✓' : '✕'}</span> <span className="pk">{KIND_LABEL[c.kind] ?? 'rule'}</span> {c.label}
      {!c.pass && <div className="pwhy">fails: {c.why}</div>}
    </li>)}
  </ul>
}

function MoveCard({ p, i, name, onPara }: { p: PowerExport; i: number; name: Names; onPara: (para: string) => void }) {
  const [all, setAll] = useState(false)
  const m = p.moves[i]
  const before = i === 0 ? p.start : p.moves[i - 1].state
  const diff = useMemo(() => diffStates(before, m.state, name), [p, i])
  return <div className={`pmove ${m.ok ? 'ok' : 'bad'}`} data-target={`pmove:${m.i}`}>
    <div className="pm-head">
      <span className={`badge ${m.ok ? 'valid' : 'failing'}`}>{m.ok ? '✓ allowed' : '✕ refused'}</span>
      <button className="linklike" onClick={() => onPara(m.para)}>¶ {m.para}</button>
      <span className="dim">move {m.i + 1} of {p.moves.length} · {m.kind}</span>
      {!m.agrees && <span className="fb" title="the module's checks and its why disagree">checks ≠ verdict</span>}
    </div>
    <div className="pm-text">{m.text}</div>
    {!m.ok && <div className="row bad">{m.why}</div>}
    <h4>Preconditions · {m.checks.filter(c => c.pass).length} of {m.checks.length} hold
      {m.checks.length > 1 && <button className="btn small" onClick={() => setAll(!all)}>{all ? 'only what fails' : 'all'}</button>}</h4>
    <Checks checks={m.checks} all={all || m.ok} />
    <h4>What it changed</h4>
    {diff.length ? <ul className="pdiff">{diff.map((d, k) => <li key={k}>{d}</li>)}</ul> : <div className="row dim">nothing in the rules' state</div>}
  </div>
}

function ActorCards({ p, s, name, onlyChanged, before }: { p: PowerExport; s: PState; name: Names; onlyChanged: boolean; before: PState }) {
  const ids = p.actors.map(a => a.id).filter(id => {
    const a = s.actors[id]
    if (!a) return false
    if (!onlyChanged) return a.status.includes('present') || a.marks.length > 0 || Object.keys(a.resources).length > 0
    return JSON.stringify(a) !== JSON.stringify(before.actors[id])
  })
  return <div className="pactors">{ids.map(id => {
    const a = s.actors[id]
    const def = p.actors.find(x => x.id === id)
    return <div key={id} className="pactor" data-target={`pactor:${id}`}>
      <div className="pa-head"><b>{name(id)}</b> <span className="dim">{def?.kind}{def?.of ? ` of ${name(def.of)}` : ''}</span>
        <span className="pstatus">{a.status.join(' · ')}</span></div>
      {Object.entries(a.resources).map(([r, n]) => {
        const max = p.resources.find(x => x.id === r)?.max[id] ?? n
        return <div key={r} className="pres"><span className="k">{r}</span>
          <span className="pbar"><span style={{ width: `${Math.min(100, (n / Math.max(1, max)) * 100)}%` }} /></span>
          <span className="v">{n} / {max}</span></div>
      })}
      {a.fields.map(f => <div key={f.key} className="pf"><span className="k">{f.label}</span><span>{show(f.value)}</span></div>)}
      {a.marks.length > 0 && <div className="pf"><span className="k">marks</span><span className="chips">{a.marks.map((m, k) =>
        <span key={k} className="chip">{m.kind} <span className="dim">· {m.via}, {name(m.by)}</span>{m.note && <i> · {m.note}</i>}</span>)}</span></div>}
    </div>
  })}</div>
}

/** Resources across all moves, one sparkline per (actor, resource), shared scale. */
function ResourceSparks({ p, i, name }: { p: PowerExport; i: number; name: Names }) {
  const rows: { key: string; label: string; values: number[] }[] = []
  for (const r of p.resources) for (const id of Object.keys(r.max)) rows.push({
    key: `${id}|${r.id}`, label: `${name(id)} · ${r.label}`,
    values: [p.start, ...p.moves.map(m => m.state)].map(s => s.actors[id]?.resources[r.id] ?? 0),
  })
  if (!rows.length) return null
  const max = Math.max(1, ...rows.flatMap(r => r.values))
  const N = p.moves.length + 1
  const x = (k: number) => (k / Math.max(1, N - 1)) * 100
  return <section><h3>Resources over the moves</h3>
    <div className="sparkgrid">{rows.map(r => <React.Fragment key={r.key}>
      <div className="sl" data-target={`pactor:${r.key.split('|')[0]}`}>{r.label}</div>
      <svg className="spark2" viewBox="0 0 100 24" preserveAspectRatio="none" height={24} aria-label={r.label}>
        <line x1={0} x2={100} y1={22} y2={22} className="sbase" />
        <polyline points={r.values.map((v, k) => `${x(k)},${22 - (v / max) * 20}`).join(' ')} fill="none" className="pline" vectorEffect="non-scaling-stroke" />
        <line x1={x(i + 1)} x2={x(i + 1)} y1={0} y2={24} className="scur" vectorEffect="non-scaling-stroke" />
      </svg>
      <div className="sv">{r.values[i + 1]}<span className="dim">/{max}</span></div>
    </React.Fragment>)}</div></section>
}

/** Standing effects (and clocks) as bars over the move axis: from the move that
 *  starts one to the move that ends it. Paragraph boundaries as ticks. */
function Lanes({ p, i, name, onMove }: { p: PowerExport; i: number; name: Names; onMove: (k: number) => void }) {
  const states = [p.start, ...p.moves.map(m => m.state)]
  const N = states.length
  const keys: { key: string; label: string; spans: [number, number][]; on: string[] }[] = []
  const find = (k: string) => keys.find(x => x.key === k)
  states.forEach((s, k) => {
    for (const e of s.active) {
      const key = `a|${e.by}|${e.what}`
      let row = find(key)
      if (!row) { row = { key, label: `${e.what} (${name(e.by)})`, spans: [], on: [] }; keys.push(row) }
      const last = row.spans[row.spans.length - 1]
      if (last && last[1] === k - 1) last[1] = k; else row.spans.push([k, k])
      for (const o of e.on) if (!row.on.includes(o)) row.on.push(o)
    }
    for (const c of s.clocks) {
      const key = `c|${c.id}`
      let row = find(key)
      if (!row) { row = { key, label: `⏱ ${c.label}`, spans: [], on: [c.target] }; keys.push(row) }
      const last = row.spans[row.spans.length - 1]
      if (last && last[1] === k - 1) last[1] = k; else row.spans.push([k, k])
    }
  })
  if (!keys.length) return null
  const bounds = p.moves.map((m, k) => k > 0 && p.moves[k - 1].para !== m.para ? k + 1 : -1).filter(k => k > 0)
  const W = N * 4
  return <section><h3>What is up, move by move</h3>
    <div className="row dim">A bar per standing effect, from the move that starts it to the move that ends it; ticks mark paragraphs; the line is the move shown.</div>
    <div className="lanegrid">{keys.map(r => <React.Fragment key={r.key}>
      <div className="ll" data-target={r.key.startsWith('a|') ? `pactive:${encodeURIComponent(r.key.slice(2))}` : undefined}>{r.label}{r.on.length > 0 && <span className="dim"> · on {r.on.map(name).join(', ')}</span>}</div>
      <svg className="lb" viewBox={`0 0 ${W} 10`} preserveAspectRatio="none" onClick={e => {
        const b = (e.currentTarget as SVGElement).getBoundingClientRect(); onMove(Math.max(0, Math.round(((e.clientX - b.left) / b.width) * N) - 1))
      }}>
        {bounds.map(k => <line key={k} x1={k * 4} x2={k * 4} y1={0} y2={10} className="ptick" />)}
        {r.spans.map(([a, b], k) => <rect key={k} x={a * 4} y={2} width={(b - a + 1) * 4} height={6} className={`pspan ${r.key[0] === 'c' ? 'clock' : ''}`} />)}
        <line x1={(i + 1) * 4 + 2} x2={(i + 1) * 4 + 2} y1={0} y2={10} className="lcur" />
      </svg>
    </React.Fragment>)}</div></section>
}

function Knowledge({ s, name }: { s: PState; name: Names }) {
  if (!s.knowledge.length) return null
  const who = [...new Set(s.knowledge.map(k => k.who))]
  const wrong = s.knowledge.filter(k => !k.true)
  return <section><h3>What they hold of the rules</h3>
    {wrong.length > 0 && <ul className="irony">{wrong.map((k, n) => <li key={n} data-target={`pknow:${k.who}`}>
      <b>{name(k.who)}</b> holds <i>{k.what}</i> <span className="ne">≠</span> it is false.</li>)}</ul>}
    {who.map(w => <details key={w} className="lanes"><summary><b>{name(w)}</b> <span className="dim">{s.knowledge.filter(k => k.who === w).length} facts</span></summary>
      <ul className="pdiff">{s.knowledge.filter(k => k.who === w).map((k, n) => <li key={n} className={k.true ? '' : 'bad'}>{k.true ? '✓' : '≠'} {k.what}</li>)}</ul></details>)}
  </section>
}

function Counterfactuals({ p, onPara }: { p: PowerExport; onPara: (para: string) => void }) {
  if (!p.counterfactuals.length) return null
  return <section><h3>Key turns: what the rules forbid</h3>
    <div className="row dim">Each is a change to the story that the module proves fails, with the move where it stops and why.</div>
    {p.counterfactuals.map(c => <div key={c.id} className="pcf" data-target={`pcf:${c.id}`}>
      <div className="pm-head"><b>{c.label}</b>{c.para && <button className="linklike" onClick={() => onPara(c.para)}>¶ {c.para}</button>}</div>
      <div className="row dim">{c.change}</div>
      <div className="row bad">{c.move !== null ? `stops at move ${c.move + 1}: ${c.why}` : c.why}</div>
      <Checks checks={c.checks} />
      <div className="row dim"><code>{c.theorem}</code> proves it.</div>
    </div>)}
  </section>
}

export function PowerView({ report, power, current, onSelect }: {
  report: Report; power: PowerExport | null; current: number; onSelect: (i: number) => void
}) {
  const p = power
  const para = report.paragraphs[current]?.name ?? ''
  // the move shown: the last of the current paragraph (or the last before it)
  const follow = useMemo(() => {
    if (!p || p.error) return 0
    let k = -1
    p.moves.forEach((m, j) => { if (m.para && m.para <= para) k = j })
    return Math.max(0, k)
  }, [p, para])
  const [i, setI] = useState(follow)
  const [changed, setChanged] = useState(true)
  useEffect(() => setI(follow), [follow])
  if (!p) return <div className="storyview dim">Reading the power system…</div>
  if (p.error) return <div className="storyview dim">{p.error.startsWith('no power export') ? 'This story has no power system export (langlib power).' : p.error}</div>
  const name = namesOf(p, report)
  const m = p.moves[i]
  const before = i === 0 ? p.start : p.moves[i - 1].state
  const goPara = (name: string) => { const k = report.paragraphs.findIndex(x => x.name === name); if (k >= 0) onSelect(k) }
  const inPara = p.moves.filter(x => x.para === m?.para)
  const bad = p.moves.filter(x => !x.ok).length
  return <div className="storyview power">
    <section>
      <h3>{p.title} <span className={`badge ${p.valid ? 'valid' : 'failing'}`}>{p.valid ? 'every move allowed' : `${bad} refused`}</span></h3>
      <div className="row dim">{p.moves.length} moves · {p.counterfactuals.length} proved key turns · from <code>{p.source}</code>
        {p.moves.some(x => !x.agrees) && <span className="bad"> · some checks disagree with the module</span>}</div>
    </section>
    {m && <section className="pscrub">
      <div className="pm-nav">
        <button className="btn small" disabled={i === 0} onClick={() => setI(i - 1)} aria-label="previous move">◀</button>
        <input type="range" min={0} max={p.moves.length - 1} value={i} onChange={e => setI(Number(e.target.value))} aria-label="move" />
        <button className="btn small" disabled={i === p.moves.length - 1} onClick={() => setI(i + 1)} aria-label="next move">▶</button>
      </div>
      <div className="pm-strip">{inPara.map(x => <button key={x.i} className={`pstep ${x.i === i ? 'on' : ''} ${x.ok ? '' : 'bad'}`}
        onClick={() => setI(x.i)} title={x.text} data-target={`pmove:${x.i}`}>{x.i + 1}</button>)}</div>
      <MoveCard p={p} i={i} name={name} onPara={goPara} />
    </section>}
    {m && <section>
      <h3>After move {i + 1}
        <label className="dim"><input type="checkbox" checked={changed} onChange={e => setChanged(e.target.checked)} /> only what changed</label></h3>
      <ActorCards p={p} s={m.state} name={name} onlyChanged={changed} before={before} />
      {m.state.relations.length > 0 && <div className="row">{m.state.relations.map((r, k) => <span key={k} className="chip" data-target={`pactor:${r.from}`}>{name(r.from)} {r.label} {name(r.to)}</span>)}</div>}
    </section>}
    <ResourceSparks p={p} i={i} name={name} />
    <Lanes p={p} i={i} name={name} onMove={setI} />
    {m && <Knowledge s={m.state} name={name} />}
    <Counterfactuals p={p} onPara={goPara} />
  </div>
}

/** Inspect a power node (right-click): a move, an actor, an effect or a key turn. */
export function PowerInspector({ power, target, report }: { power: PowerExport; target: string; report: Report }) {
  const name = namesOf(power, report)
  const [kind, ...r] = target.split(':')
  const key = r.join(':')
  if (kind === 'pmove') {
    const m = power.moves[Number(key)]
    if (!m) return <div className="storyview dim">That move is gone.</div>
    return <div className="inspector"><h3>{m.text} <span className="dim">move {m.i + 1} · ¶{m.para}</span></h3>
      <section><div className="ins-row"><span className="k">reading</span><code>{m.raw}</code></div>
        <div className="ins-row"><span className="k">verdict</span><span className={m.ok ? 'ok' : 'bad'}>{m.ok ? 'allowed' : `refused: ${m.why}`}</span></div>
        <h4>Every precondition</h4><Checks checks={m.checks} all /></section></div>
  }
  if (kind === 'pactor') {
    const id = key.split('|')[0]
    const hist = power.moves.filter(m => m.actor === id || m.targets.includes(id))
    return <div className="inspector"><h3>{name(id)} <span className="dim">{power.actors.find(a => a.id === id)?.kind}</span></h3>
      <section><h4>Moves by or on them · {hist.length}</h4><ul className="pdiff">{hist.map(m => <li key={m.i} className={m.ok ? '' : 'bad'}>¶{m.para} · {m.text}</li>)}</ul></section></div>
  }
  if (kind === 'pactive') {
    const [by, ...w] = decodeURIComponent(key).split('|'); const what = w.join('|')
    const spans = power.moves.filter(m => m.state.active.some(a => a.by === by && a.what === what))
    return <div className="inspector"><h3>{what} <span className="dim">{name(by)}</span></h3>
      <section><div className="ins-row"><span className="k">up during</span><span>{spans.length} moves: ¶{[...new Set(spans.map(m => m.para))].join(', ¶')}</span></div></section></div>
  }
  if (kind === 'pcf') {
    const c = power.counterfactuals.find(x => x.id === key)
    if (!c) return <div className="storyview dim">That key turn is gone.</div>
    return <div className="inspector"><h3>{c.label} <span className="dim">key turn</span></h3>
      <section><div className="ins-row"><span className="k">the change</span><span>{c.change}</span></div>
        <div className="ins-row"><span className="k">stops</span><span className="bad">{c.move !== null ? `move ${c.move + 1}, ¶${c.para}: ` : ''}{c.why}</span></div>
        <div className="ins-row"><span className="k">proved by</span><code>{c.theorem}</code></div>
        <h4>The stopped move's preconditions</h4><Checks checks={c.checks} all /></section></div>
  }
  return <div className="storyview dim">{target}</div>
}

export const POWER_KINDS = new Set(['pmove', 'pactor', 'pactive', 'pcf', 'pcheck', 'pknow'])
