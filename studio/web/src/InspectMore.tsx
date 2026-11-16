import React from 'react'
import type { Readings, Report } from './types'
import { charColour, charName } from './Logic'
import { ArgTreeView } from './ArgTree'
import { argNodeInfo } from './Argument'
import { consentScenes, parseFeel, parseTie } from './readings'

/** Right-click → Inspect for what the new views draw: argument nodes,
 *  beliefs, nested beliefs, ties, feelings, consent lanes, identity rows,
 *  style rules. Read-only: these come from the prose's reading, so they change
 *  through the prose (or by asking the agent). */

export const MORE_KINDS = new Set(['arg', 'belief', 'nested', 'tie', 'feel', 'consent', 'ident', 'rule', 'style', 'needs'])

const parts = (t: string) => { const [kind, ...r] = t.split(':'); return [kind, ...((kind === 'rule' || kind === 'style') ? r.map(decodeURIComponent) : r)] }

export function describeMore(report: Report, t: string): string | null {
  const [kind, ...r] = parts(t)
  const C = (id: string) => charName(report, id)
  const atom = (b: string) => report.atoms.find(a => a.id === b)?.label ?? b
  switch (kind) {
    case 'arg': { const n = report.argument?.nodes.find(x => x.id === r.join(':')); return n ? `argument “${n.gloss}”` : 'argument node' }
    case 'belief': return `${C(r[0])}'s belief “${atom(r.slice(1).join(':'))}”`
    case 'nested': return `what ${C(r[0])} thinks ${C(r[1])} thinks of “${atom(r.slice(2).join(':'))}”`
    case 'tie': return `${C(r[0])} ${r[1]} ${C(r[2])}`
    case 'feel': return `${C(r[0])}'s ${r[1]}`
    case 'consent': return `consent: ${C(r[0])} → ${C(r[1])}, ${r[2]}`
    case 'ident': return `what ${C(r[0])} knows of ${C(r[1])}`
    case 'needs': return `${C(r[0])}'s needs`
    case 'rule': return `style rule “${r[2]}” (${r[0]} · ${r[1]})`
    case 'style': return `style “${r[1]}” (${r[0]})`
  }
  return null
}

function Row({ k, children }: { k: string; children: React.ReactNode }) {
  return <div className="ins-row"><span className="k">{k}</span><span>{children}</span></div>
}

export function MoreInspector({ report, readings, target, current, onAsk }: {
  report: Report; readings: Readings | null; target: string; current: number; onAsk: () => void
}) {
  const [kind, ...r] = parts(target)
  const C = (id: string) => <b style={{ color: charColour(report, id) }}>{charName(report, id)}</b>
  const states = [report.start, ...report.paragraphs.map(p => p.state)]
  const pname = (k: number) => k === 0 ? 'start' : `¶${report.paragraphs[k - 1].name}`
  let body: React.ReactNode = null
  if (kind === 'arg') {
    const info = argNodeInfo(report, r.join(':'))
    body = !info ? <div className="dim">That node is gone (the reading changed).</div> : <>
      <section>
        <Row k="kind">{info.n.kind}{info.n.who ? <> of {C(info.n.who)}</> : null}, ¶{info.n.para}</Row>
        <Row k="literal"><code>{info.n.lit}</code></Row>
        <Row k="label">{info.n.status.toUpperCase()}{info.n.note ? ` · ${info.n.note}` : ''}</Row>
        {info.inn.length > 0 && <Row k="from"><ul className="ins-list">{info.inn.map((e, i) => <li key={i}>{e.kind}: {info.name(e.src)} ({e.why})</li>)}</ul></Row>}
        {info.out.length > 0 && <Row k="to"><ul className="ins-list">{info.out.map((e, i) => <li key={i}>{e.kind}: {info.name(e.tgt)} ({e.why})</li>)}</ul></Row>}
      </section>
      {info.tree && info.tree.kids.length > 0 && <section><h4>Its tree</h4><ArgTreeView t={info.tree} openDepth={3} /></section>}
    </>
  } else if (kind === 'belief' || kind === 'nested') {
    const who = r[0], about = kind === 'nested' ? r[1] : '', base = r.slice(kind === 'nested' ? 2 : 1).join(':')
    const hist = states.map((s, k) => {
      const l = (s.views[who] ?? []).find(x => x.lit.replace(/^!/, '') === base)
      return { k, l }
    })
    const gains = report.paragraphs.flatMap(p => p.delta.beliefs.filter(b => b.who === who && b.lit.replace(/^!/, '') === base).map(b => ({ p: p.name, b })))
    const nests = report.paragraphs.flatMap(p => p.delta.nested.filter(n => n.who === who && n.about === about && n.lit.replace(/^!/, '') === base).map(n => ({ p: p.name, n })))
    body = <section>
      <Row k="whose">{C(who)}{about && <> about {C(about)}</>}</Row>
      {kind === 'belief' ? <Row k="over the story"><ul className="ins-list">{hist.filter(h => h.l).map(h => <li key={h.k}>{pname(h.k)}: {h.l!.lit.startsWith('!') ? 'thinks not' : 'thinks so'}{h.l!.true ? '' : <span className="fb">false</span>}</li>)}</ul></Row>
        : <Row k="over the story"><ul className="ins-list">{nests.map((x, i) => <li key={i}>¶{x.p}: {x.n.gloss}{!x.n.accurate && <span className="fb">wrong</span>}</li>)}</ul></Row>}
      {gains.length > 0 && <Row k="changes"><ul className="ins-list">{gains.map((g, i) => <li key={i}>¶{g.p}: {g.b.change} “{g.b.gloss}”{g.b.explain.map((x, j) => <div key={j} className="dim">{x.src}: {x.reasons.map(([a, n]) => `${a} ${n >= 0 ? '+' : ''}${n}`).join(', ')} = {x.strength}; {x.attitude}; {x.status}</div>)}</li>)}</ul></Row>}
    </section>
  } else if (kind === 'tie' || kind === 'feel') {
    const ext = readings?.ext
    const vals = (ext?.paragraphs ?? []).map(p => kind === 'tie'
      ? p.ties.map(parseTie).find(t => t && t.a === r[0] && t.rel === r[1] && t.b === r[2])?.n ?? 0
      : p.feels.map(parseFeel).find(f => f && f.who === r[0] && f.emo === r[1])?.n ?? 0)
    const evs = (ext?.paragraphs ?? []).flatMap(p => p.events.filter(e => kind === 'tie' ? e.e.includes(` ${r[1]} `) && e.e.includes(r[0]) && e.e.includes(r[2]) : e.e.includes(r[0])).map(e => ({ ...e, para: p.name })))
    body = <section>
      <Row k="now">{vals[current] ?? 0}</Row>
      <Row k="over the story">{vals.map((v, i) => <span key={i} className={i === current ? 'chip on' : 'chip'}>¶{ext!.paragraphs[i].name}: {v}</span>)}</Row>
      {evs.length > 0 && <Row k="events"><ul className="ins-list">{evs.slice(0, 20).map((e, i) => <li key={i}>¶{e.para}: {e.e}{!e.ok && <span className="bad"> refused: {e.why}</span>}</li>)}</ul></Row>}
    </section>
  } else if (kind === 'consent') {
    const evs = readings?.consent ? consentScenes(readings.consent).flatMap(s => s.events).filter(e => e.act === r[2] &&
      ((e.kind === 'grant' || e.kind === 'withdraw') ? e.a === r[0] && e.b === r[1] : e.b === r[0] && e.a === r[1])) : []
    body = <section>
      <Row k="who">{C(r[0])} → {C(r[1])}: {r[2]}</Row>
      <Row k="events"><ul className="ins-list">{evs.map((e, i) => <li key={i} className={e.status === 'yes' ? '' : e.status === 'no' ? 'bad' : 'warn'}>¶{e.para}: {e.raw} · {e.status === 'yes' ? 'allowed' : e.status === 'no' ? 'refused' : 'assumed'}{e.why ? ` (${e.why})` : ''}</li>)}</ul></Row>
    </section>
  } else if (kind === 'ident' || kind === 'needs') {
    const ext = readings?.ext
    const p = ext?.paragraphs[current]
    body = <section>
      {kind === 'ident' ? <Row k="knows">{(p?.knows ?? []).filter(k => k.who === r[0] && k.of === r[1]).map((k, i) => <span key={i} className="chip">{k.kind}: {k.v}{k.right === false ? ' (wrong)' : ''}</span>)}</Row>
        : <Row k="needs">{(p?.needs ?? []).find(s => s.startsWith(`${r[0]}:`)) ?? 'none'}</Row>}
      <Row k="events"><ul className="ins-list">{(ext?.paragraphs ?? []).flatMap(q => q.events.filter(e => e.e.includes(` ${r[0]} `) || e.e.endsWith(` ${r[0]}`)).map((e, i) => <li key={q.name + i}>¶{q.name}: {e.e}</li>)).slice(0, 30)}</ul></Row>
    </section>
  } else if (kind === 'rule' || kind === 'style') {
    const src = r[0] === 'house' ? readings?.house : readings?.style
    const s = src?.styles.find(x => x.name === r[1])
    const rules = kind === 'rule' ? s?.rules.filter(x => x.name === r[2]) : s?.rules
    body = <section>
      <Row k="from"><code>langlib {r[0]}</code>, style {r[1]}</Row>
      <Row k="rules"><ul className="ins-list">{(rules ?? []).map(x => <li key={x.name} className={x.holds ? 'ok' : 'bad'}>{x.holds ? '✓' : '✕'} {x.name}: <code>{x.rule}</code></li>)}</ul></Row>
      {src?.features && <Row k="measured"><span className="chips">{Object.entries(src.features).map(([k, v]) => <span key={k} className="chip">{k} {String(v)}</span>)}</span></Row>}
    </section>
  }
  return <div className="inspector">
    <h3>{describeMore(report, target)} <span className="dim">{kind}</span></h3>
    {body}
    <div className="ins-foot"><button className="btn" onClick={onAsk}>Ask the agent…</button>
      <div className="dim">Read off the prose and its reading; it changes through them.</div></div>
  </div>
}
