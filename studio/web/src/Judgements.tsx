import React, { useState } from 'react'
import type { Completeness, Deriv, Report, TreeJ } from './types'

/** Completeness in the Studio: each clause of a paragraph with the judgements that tie it to the
 *  world, the connectives between clauses with their verdict, and what the checker objects to. */

export const KIND_LABEL: Record<string, string> = {
  event: 'event', claim: 'claim', content: 'content', goal: 'goal', act: 'gesture',
  speech: 'speech', hypothetical: 'hypothetical', external: 'Nen move',
}

const REL_LABEL: Record<string, string> = {
  cause: 'cause', effect: 'cause', purpose: 'purpose', after: 'after', before: 'before',
  during: 'at the same time', concession: 'both hold', condition: 'hypothetical',
}

export function compOf(report: Report, name: string): Completeness | undefined {
  return report.completeness?.find(c => c.name === name)
}

/** Tokens the checker objects to (its messages name them as "(token N)"). */
export function badTokens(c: Completeness): Set<number> {
  const out = new Set<number>()
  for (const i of c.issues) for (const m of i.matchAll(/\(token (\d+)\)/g)) out.add(Number(m[1]))
  return out
}

export interface TokJudgement {
  clause?: { w: string; neg: boolean; modal: boolean; quoted: boolean }
  judges: { kind: string; text: string; gloss: string }[]
  link?: { word: string; rel: string; ok: boolean; a: string; b: string }
  bad: boolean
}

/** What completeness says about each token of a paragraph. */
export function byToken(c: Completeness): Map<number, TokJudgement> {
  const bad = badTokens(c)
  const word = (t: number) => c.clauses.find(x => x.at === t)?.w ?? `token ${t}`
  const m = new Map<number, TokJudgement>()
  const get = (t: number) => { if (!m.has(t)) m.set(t, { judges: [], bad: bad.has(t) }); return m.get(t)! }
  for (const cl of c.clauses) get(cl.at).clause = cl
  for (const j of c.judges) get(j.at).judges.push(j)
  for (const l of c.links) if (l.a !== l.b)
    get(l.at).link = { word: l.word, rel: l.rel, ok: !bad.has(l.at), a: word(l.a), b: word(l.b) }
  return m
}

/** Clause heads along a line, a dot per judgement, connectives as arcs between clauses. */
function Arcs({ c }: { c: Completeness }) {
  const bad = badTokens(c)
  const clauses = [...c.clauses].sort((x, y) => x.at - y.at)
  const step = 66, pad = 30
  const x = (t: number) => pad + Math.max(0, clauses.findIndex(cl => cl.at === t)) * step
  const links = c.links.filter(l => l.a !== l.b)
  const maxSpan = Math.max(1, ...links.map(l => Math.abs(x(l.a) - x(l.b))))
  const arcH = Math.min(46, 14 + maxSpan * 0.16)
  const width = pad * 2 + Math.max(0, clauses.length - 1) * step
  const base = arcH + 16
  const height = base + 34
  return (
    <div className="jarcs-wrap">
      <svg className="jarcs" width={width} height={height}>
        {links.map((l, i) => {
          const xa = x(l.a), xb = x(l.b), mid = (xa + xb) / 2
          const h = 10 + Math.abs(xb - xa) * 0.16
          const ok = !bad.has(l.at)
          return (
            <g key={i} className={`jlink r-${l.rel} ${ok ? 'ok' : 'bad'}`}>
              <path d={`M ${xa} ${base - 12} Q ${mid} ${base - 12 - 2 * h} ${xb} ${base - 12}`} markerEnd="url(#jarrow)" />
              <text x={mid} y={base - 14 - h} textAnchor="middle">{l.word} {ok ? '✓' : '✗'}</text>
              <title>{`'${l.word}': ${REL_LABEL[l.rel] ?? l.rel}, from “${clauses.find(cl => cl.at === l.a)?.w}” to “${clauses.find(cl => cl.at === l.b)?.w}”${ok ? '' : ' — refused'}`}</title>
            </g>)
        })}
        <defs><marker id="jarrow" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="6" markerHeight="6" orient="auto">
          <path d="M0,0 L8,4 L0,8 z" className="jarrowhead" /></marker></defs>
        {clauses.map(cl => {
          const js = c.judges.filter(j => j.at === cl.at)
          return (
            <g key={cl.at} className={`jclause ${bad.has(cl.at) || js.length === 0 ? 'bad' : ''}`} data-target={`tok:${c.name}:${cl.at}`}>
              <text x={x(cl.at)} y={base} textAnchor="middle" className="w">{cl.w}</text>
              {(js.length ? js : [{ kind: 'missing', text: 'no judgement', gloss: 'no judgement' }]).map((j, k) => (
                <circle key={k} cx={x(cl.at) + (k - (Math.max(js.length, 1) - 1) / 2) * 9} cy={base + 11} r={3.4}
                  className={`jdot k-${j.kind}`}><title>{`${KIND_LABEL[j.kind] ?? j.kind}: ${j.gloss}`}</title></circle>))}
            </g>)
        })}
      </svg>
    </div>
  )
}


/** One sentence as a tree: nodes above, words at the bottom, and under every clause head the
 *  judgements that tie it to the world; connectives as arcs below them. */
function SentenceTree({ c, tree, start }: { c: Completeness; tree: TreeJ; start: number }) {
  const bad = badTokens(c)
  const CH = 6.4, LV = 22, PAD = 8
  type Leaf = { x: number; w: string; p: string; i: number; ref?: string; sense?: string }
  type Node = { x: number; lvl: number; label: string; kids: { x: number; lvl: number }[] }
  const leaves: Leaf[] = [], nodes: Node[] = []
  let x = PAD, i = start
  const level = (t: TreeJ): number => t.w !== undefined ? 0 : 1 + Math.max(...(t.k ?? []).map(level))
  const lay = (t: TreeJ): { x: number; lvl: number } => {
    if (t.w !== undefined) {
      const w = Math.max(t.w.length * CH * 1.25, 26) + 6
      const cx = x + w / 2
      x += w
      leaves.push({ x: cx, w: t.w, p: t.p ?? '', i: i++, ref: t.ref, sense: t.sense })
      return { x: cx, lvl: 0 }
    }
    const kids = (t.k ?? []).map(lay)
    const cx = kids.reduce((a, k) => a + k.x, 0) / Math.max(1, kids.length)
    const lvl = level(t)
    nodes.push({ x: cx, lvl, label: (t.c ?? '') + (t.ref ? `→${t.ref}` : ''), kids })
    return { x: cx, lvl }
  }
  lay(tree)
  const width = x + PAD
  const top = Math.max(1, ...nodes.map(n => n.lvl)) * LV + 10
  const wordY = top + 4
  const yOf = (lvl: number) => top - lvl * LV
  // judgements under clause heads, stacked so boxes on a level do not overlap
  const own = (t: number) => c.judges.filter(j => j.at === t)
  const boxes: { x: number; y: number; w: number; kind: string; text: string; tip: string; i: number }[] = []
  const levels: [number, number][][] = []
  const J0 = wordY + 30, JH = 17
  for (const l of leaves) {
    const isClause = c.clauses.some(cl => cl.at === l.i)
    const js = own(l.i)
    const items = js.length ? js : isClause ? [{ kind: 'missing', text: 'no judgement', gloss: 'no judgement', at: l.i }] : []
    let d = 0
    for (const j of items) {
      const label = `${KIND_LABEL[j.kind] ?? j.kind}: ${j.kind === 'event' || j.kind === 'claim' || j.kind === 'external' ? j.text : j.gloss}`
      const w = label.length * 5.6 + 10
      const lo = l.x - w / 2 - 3, hi = l.x + w / 2 + 3
      while (d < levels.length && levels[d].some(([a, b]) => !(hi < a || lo > b))) d++
      if (d === levels.length) levels.push([])
      levels[d].push([lo, hi])
      boxes.push({ x: l.x, y: J0 + d * JH, w, kind: j.kind, text: label, tip: j.gloss, i: l.i })
      d++
    }
  }
  const jBottom = J0 + Math.max(0, levels.length - 1) * JH + 10
  const toks = new Set(leaves.map(l => l.i))
  const links = c.links.filter(l => l.a !== l.b && toks.has(l.a) && toks.has(l.b))
  const xOf = (t: number) => leaves.find(l => l.i === t)?.x ?? 0
  const sag = (l: { a: number; b: number }) => 10 + Math.abs(xOf(l.a) - xOf(l.b)) * 0.12
  const height = jBottom + (links.length ? Math.max(...links.map(sag)) + 20 : 6)
  const minX = Math.min(...leaves.map(l => l.x)), maxX = Math.max(...leaves.map(l => l.x))
  const right = Math.max(width, ...boxes.map(b => b.x + b.w / 2 + 4))
  const left = Math.min(0, ...boxes.map(b => b.x - b.w / 2 - 4))
  void minX; void maxX
  return (
    <svg className="jtree" width={right - left} height={height} viewBox={`${left} 0 ${right - left} ${height}`}>
      {nodes.map((n, k) => <g key={k}>
        {n.kids.map((kd, m) => <line key={m} x1={n.x} y1={yOf(n.lvl) + 4} x2={kd.x} y2={kd.lvl === 0 ? wordY - 11 : yOf(kd.lvl) - 6} className="edge" />)}
        <text x={n.x} y={yOf(n.lvl)} textAnchor="middle" className="nlabel">{n.label}</text>
      </g>)}
      {leaves.map(l => {
        const isClause = c.clauses.some(cl => cl.at === l.i)
        const js = own(l.i)
        const kind = js[0]?.kind
        const link = c.links.find(k => k.at === l.i && k.a !== k.b)
        const cls = ['word', isClause ? 'clause' : '', isClause && (bad.has(l.i) || !js.length) ? 'bad' : '',
          isClause && kind ? `k-${kind}` : '', link ? (bad.has(l.i) ? 'conn bad' : 'conn') : ''].join(' ')
        return <g key={l.i} data-target={isClause ? `tok:${c.name}:${l.i}` : undefined}>
          <text x={l.x} y={wordY} textAnchor="middle" className={cls}>{l.w}</text>
          <text x={l.x} y={wordY + 11} textAnchor="middle" className={`pos ${l.sense && (l.p === 'ADV' || l.p === 'ADJ') ? 'sense' : ''}`}>
            {l.p}{l.sense && (l.p === 'ADV' || l.p === 'ADJ') ? `·${l.sense}` : ''}</text>
        </g>
      })}
      {boxes.map((b, k) => <g key={k} className={`jbox k-${b.kind} ${bad.has(b.i) ? 'bad' : ''}`}>
        {boxes.findIndex(o => o.i === b.i) === k && <line x1={b.x} y1={wordY + 15} x2={b.x} y2={b.y - 6} className="stem" />}
        <rect x={b.x - b.w / 2} y={b.y - 6} width={b.w} height={13} rx={4} />
        <text x={b.x} y={b.y + 3.5} textAnchor="middle">{b.text}</text>
        <title>{b.tip}</title>
      </g>)}
      {links.map((l, k) => {
        const xa = xOf(l.a), xb = xOf(l.b), ok = !bad.has(l.at), h = sag(l)
        return <g key={k} className={`jlink r-${l.rel} ${ok ? 'ok' : 'bad'}`}>
          <path d={`M ${xa} ${jBottom} Q ${(xa + xb) / 2} ${jBottom + 2 * h} ${xb} ${jBottom}`} markerEnd="url(#jarrow2)" />
          <text x={(xa + xb) / 2} y={jBottom + h + 13} textAnchor="middle">‘{l.word}’ {REL_LABEL[l.rel] ?? l.rel} {ok ? '✓' : '✗'}</text>
        </g>
      })}
      <defs><marker id="jarrow2" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="6" markerHeight="6" orient="auto">
        <path d="M0,0 L8,4 L0,8 z" className="jarrowhead" /></marker></defs>
    </svg>
  )
}

function Trees({ c }: { c: Completeness }) {
  const count = (t: TreeJ): number => t.w !== undefined ? 1 : (t.k ?? []).reduce((a, k) => a + count(k), 0)
  let start = 0
  return <div className="jtrees">{(c.trees ?? []).map((t, k) => {
    const s = start
    start += count(t)
    return <div key={k} className="jtree-wrap"><SentenceTree c={c} tree={t} start={s} /></div>
  })}</div>
}

/** A derivation as a Gentzen-style proof tree: premises above the line, the rule beside it,
 *  the conclusion below. */
export function Derivation({ d }: { d: Deriv }) {
  return (
    <div className={`inf ${d.ok ? '' : 'bad'}`}>
      {d.prems.length > 0 && <div className="prems">{d.prems.map((p, k) => <Derivation key={k} d={p} />)}</div>}
      <div className="bar"><span className="line" /><span className="rule">{d.rule}</span></div>
      <div className="concl">{d.concl}</div>
    </div>
  )
}

function Rules({ c }: { c: Completeness }) {
  return <div className="jrules">{(c.derivations ?? []).map((x, k) =>
    <div key={k} className="jrule-wrap"><Derivation d={x.d} /></div>)}</div>
}

export function JudgementSection({ c }: { report: Report; c: Completeness }) {
  const [view, setView] = useState<'tree' | 'rules' | 'list'>('tree')
  const bad = badTokens(c)
  const clauses = [...c.clauses].sort((x, y) => x.at - y.at)
  return (
    <div className="judge-sec">
      <div className={`row ${c.issues.length ? 'bad' : 'ok'}`}>
        {c.issues.length ? `${c.issues.length} objection${c.issues.length > 1 ? 's' : ''}` : `complete: ${clauses.length} clauses, each judged by the world`}
      </div>
      <div className="jview">
        {(['tree', 'rules', 'list'] as const).map(v => <button key={v} className={view === v ? 'on' : ''}
          onClick={e => { e.stopPropagation(); setView(v) }}>{v}</button>)}
      </div>
      {view === 'tree' && c.trees ? <Trees c={c} /> : view === 'rules' ? <Rules c={c} /> : <><Arcs c={c} />
      <ul className="jlist">{clauses.map(cl => {
        const js = c.judges.filter(j => j.at === cl.at)
        return (
          <li key={cl.at} className={bad.has(cl.at) || js.length === 0 ? 'bad' : ''} data-target={`tok:${c.name}:${cl.at}`}>
            <b className="jw">{cl.w}</b>
            {cl.neg && <span className="jflag">not</span>}{cl.modal && <span className="jflag">modal</span>}{cl.quoted && <span className="jflag">quoted</span>}
            {js.length === 0 && <span className="jchip k-missing">no judgement</span>}
            {js.map((j, k) => <span key={k} className={`jchip k-${j.kind}`} title={j.text}>
              <i>{KIND_LABEL[j.kind] ?? j.kind}</i>{['act', 'speech', 'hypothetical'].includes(j.kind) ? null : <> {j.kind === 'event' || j.kind === 'content' || j.kind === 'goal' ? j.gloss : j.text}</>}</span>)}
          </li>)
      })}</ul></>}
      {c.issues.map((i, k) => <div key={k} className="row bad jissue">✗ {i}</div>)}
    </div>
  )
}

/** The story's judgements alone: every clause in story order with what the world says of it, the
 *  connectives with their verdicts, and the objections; no prose, no trees. */
export function JudgementsView({ report, onSelect }: { report: Report; onSelect: (i: number) => void }) {
  const [only, setOnly] = useState<string | null>(null)
  const [as, setAs] = useState<'list' | 'rules'>('list')
  const comps = report.completeness ?? []
  const all = comps.flatMap(c => c.judges)
  const kinds = [...new Set(all.map(j => j.kind))]
  const issues = comps.reduce((n, c) => n + c.issues.length, 0)
  const clauses = comps.reduce((n, c) => n + c.clauses.length, 0)
  const links = comps.flatMap(c => c.links.filter(l => l.a !== l.b))
  return (
    <div className="jview-all">
      <div className={`row ${issues ? 'bad' : 'ok'}`}>
        {issues ? `${issues} objection${issues > 1 ? 's' : ''}` : 'complete'} · {clauses} clauses · {all.length} judgements · {links.length} connectives checked
      </div>
      <div className="jview">
        {(['list', 'rules'] as const).map(v => <button key={v} className={as === v ? 'on' : ''} onClick={() => setAs(v)}>{v}</button>)}
      </div>
      <div className="jfilter">
        <button className={only === null ? 'on' : ''} onClick={() => setOnly(null)}>all</button>
        {kinds.map(k => <button key={k} className={`jchip k-${k} ${only === k ? 'on' : ''}`}
          onClick={() => setOnly(only === k ? null : k)}>{KIND_LABEL[k] ?? k} {all.filter(j => j.kind === k).length}</button>)}
        <button className={`jchip k-link ${only === 'link' ? 'on' : ''}`} onClick={() => setOnly(only === 'link' ? null : 'link')}>connectives {links.length}</button>
        {issues > 0 && <button className={`jchip k-missing ${only === 'bad' ? 'on' : ''}`} onClick={() => setOnly(only === 'bad' ? null : 'bad')}>objections {issues}</button>}
      </div>
      {comps.map(c => {
        const pi = report.paragraphs.findIndex(p => p.name === c.name)
        const bad = badTokens(c)
        const word = (t: number) => c.clauses.find(x => x.at === t)?.w ?? `token ${t}`
        type Row = { at: number; node: React.ReactNode; bad: boolean; kinds: string[] }
        const rows: Row[] = []
        for (const cl of c.clauses) {
          const js = c.judges.filter(j => j.at === cl.at)
          rows.push({ at: cl.at, bad: bad.has(cl.at) || js.length === 0, kinds: js.map(j => j.kind), node: <>
            <b className="jw">{cl.w}</b>
            {js.length === 0 && <span className="jchip k-missing">no judgement</span>}
            {js.map((j, k) => <span key={k} className={`jchip k-${j.kind}`} title={j.text}>
              <i>{KIND_LABEL[j.kind] ?? j.kind}</i>{['act', 'speech', 'hypothetical'].includes(j.kind) ? null : <> {j.kind === 'event' || j.kind === 'content' || j.kind === 'goal' ? j.gloss : j.text}</>}</span>)}
          </> })
        }
        for (const l of c.links.filter(l => l.a !== l.b)) {
          const ok = !bad.has(l.at)
          rows.push({ at: l.at + 0.5, bad: !ok, kinds: ['link'], node: <span className={`jconn r-${l.rel} ${ok ? 'ok' : 'bad'}`}>
            ‘{l.word}’ <span className="dim">{word(l.a)} → {word(l.b)}</span> {l.rel} {ok ? '✓' : '✗'}</span> })
        }
        const shown = rows.sort((a, b) => a.at - b.at).filter(r =>
          only === null || (only === 'bad' ? r.bad : r.kinds.includes(only)))
        if (!shown.length && !(only === 'bad' && c.issues.length)) return null
        if (as === 'rules') {
          const ds = (c.derivations ?? []).filter(x => only === null ||
            (only === 'bad' ? !x.d.ok : only === 'link' ? c.links.some(l => l.at === x.at && l.a !== l.b)
              : c.judges.some(j => j.at === x.at && j.kind === only)))
          if (!ds.length) return null
          return <div key={c.name} className="jpara" onClick={() => onSelect(pi)}>
            <div className="jpn">¶ {c.name}</div>
            <div className="jrules">{ds.map((x, k) => <div key={k} className="jrule-wrap"><Derivation d={x.d} /></div>)}</div>
          </div>
        }
        return <div key={c.name} className="jpara" onClick={() => onSelect(pi)}>
          <div className="jpn">¶ {c.name}</div>
          <ul className="jlist">{shown.map((r, k) => <li key={k} className={r.bad ? 'bad' : ''}>{r.node}</li>)}</ul>
          {(only === null || only === 'bad') && c.issues.map((i, k) => <div key={k} className="row bad jissue">✗ {i}</div>)}
        </div>
      })}
    </div>
  )
}
