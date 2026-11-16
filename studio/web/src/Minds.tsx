import React, { useMemo, useState } from 'react'
import type { Explain, Report } from './types'
import { charColour, charName } from './Logic'

/** Epistemic views per character (docs/ui-visualisation.md §8):
 *  - now: characters × propositions at the current paragraph, belief and fact
 *    in one cell, a false belief outlined with ≠ ("thinks / actually");
 *    strength as lightness (outright, provisional, only noted);
 *  - sources: a cell's justification, filtered to that belief, with trust;
 *  - through their eyes: what one character thinks the others think, as chip
 *    paths A → B → p;
 *  - dramatic irony: false beliefs at the current paragraph, and whether the
 *    reader has been shown the truth;
 *  - over time: a lane per character, a bar per belief, hatched where false. */

type Sign = 'yes' | 'no'
interface Row { base: string; label: string; truth: boolean | null }

const baseOf = (lit: string) => lit.replace(/^!/, '')
const signOf = (lit: string): Sign => lit.startsWith('!') ? 'no' : 'yes'
const shown = (lit: string) => !baseOf(lit).startsWith('at(')

/** Per paragraph (0 = start), each character's view as base → sign and truth. */
function viewsOver(report: Report) {
  const states = [report.start, ...report.paragraphs.map(p => p.state)]
  return states.map(s => {
    const m: Record<string, Map<string, { sign: Sign; ok: boolean; gloss: string }>> = {}
    for (const c of report.characters) {
      m[c.id] = new Map()
      for (const l of s.views[c.id] ?? []) if (shown(l.lit)) m[c.id].set(baseOf(l.lit), { sign: signOf(l.lit), ok: l.true, gloss: l.gloss })
    }
    return m
  })
}

/** The latest justification of each (who, base), from the belief deltas up to paragraph i. */
function explainsUpTo(report: Report, i: number) {
  const m = new Map<string, { explain: Explain[]; para: string }>()
  report.paragraphs.slice(0, i + 1).forEach(p => {
    for (const b of p.delta.beliefs) if (b.change === 'gained') m.set(`${b.who}|${baseOf(b.lit)}`, { explain: b.explain, para: p.name })
  })
  return m
}

/** Nested beliefs held by paragraph i: who thinks about thinks lit (latest wins). */
function nestedUpTo(report: Report, i: number) {
  const m = new Map<string, { who: string; about: string; lit: string; gloss: string; accurate: boolean; para: string }>()
  report.paragraphs.slice(0, i + 1).forEach(p => {
    for (const n of p.delta.nested) if (shown(n.lit)) m.set(`${n.who}|${n.about}|${baseOf(n.lit)}`, { ...n, para: p.name })
  })
  return [...m.values()]
}

const ATT: Record<string, string> = { radical: 'outright', hard: 'outright', conservative: 'provisional', note: 'only noted' }
const srcText = (report: Report, s: string) => s.startsWith('told:') ? `told by ${charName(report, s.slice(5))}` : s

function Sources({ report, who, base, i, onClose }: { report: Report; who: string; base: string; i: number; onClose: () => void }) {
  const ex = explainsUpTo(report, i).get(`${who}|${base}`)
  const bonds = (report.paragraphs[i]?.state ?? report.start).bonds
  return <div className="sources" data-target={`belief:${who}:${base}`}>
    <div className="row"><b style={{ color: charColour(report, who) }}>{charName(report, who)}</b>'s grounds for this belief{ex ? `, formed in ¶${ex.para}` : ''}
      <button className="btn small" onClick={onClose}>close</button></div>
    {!ex ? <div className="row dim">held from the start (background) or kept from before the paragraphs; no source recorded.</div> :
      <ul className="explain">{ex.explain.map((x, j) => {
        const speaker = x.src.startsWith('told:') ? x.src.slice(5) : null
        const trust = speaker ? bonds[`${who}>${speaker}`]?.trust : undefined
        return <li key={j}><b>{srcText(report, x.src)}</b>{trust !== undefined && <span className="dim"> (trusts them {trust})</span>}:
          {' '}{x.reasons.map(([r, n]) => `${r} ${n >= 0 ? '+' : ''}${n}`).join(', ')} = {x.strength}; taken {ATT[x.attitude] ?? x.attitude}; <i>{x.status}</i>{x.caught ? ' (caught out)' : ''}</li>
      })}</ul>}
  </div>
}

export function MindsView({ report, current }: { report: Report; current: number }) {
  const views = useMemo(() => viewsOver(report), [report])
  const i = Math.max(0, current)
  const now = views[i + 1] ?? views[0]
  const [eyes, setEyes] = useState<string>('')
  const [cell, setCell] = useState<{ who: string; base: string } | null>(null)
  const [onlyFalse, setOnlyFalse] = useState(false)
  const ex = useMemo(() => explainsUpTo(report, i), [report, i])
  const chars = report.characters
  const atoms = new Map(report.atoms.map(a => [a.id, a]))
  // rows: what anyone holds now
  const rows: Row[] = []
  const seen = new Set<string>()
  for (const c of chars) for (const [base, v] of now[c.id]) if (!seen.has(base)) {
    seen.add(base)
    const a = atoms.get(base)
    rows.push({ base, label: a?.label ?? v.gloss.replace(/^not: /, ''), truth: v.sign === 'yes' ? v.ok : !v.ok })  // the world now, not at the start
  }
  const wrongAny = (r: Row) => chars.some(c => { const v = now[c.id].get(r.base); return v && !v.ok })
  const tableRows = rows.filter(r => !onlyFalse || wrongAny(r)).sort((a, b) => Number(wrongAny(b)) - Number(wrongAny(a)))
  const facts = new Map((report.argument?.nodes ?? []).filter(n => n.kind === 'fact').map(n => [n.lit, n.para]))
  const paraIdx = (name: string) => report.paragraphs.findIndex(p => p.name === name)
  const irony = chars.flatMap(c => [...now[c.id]].filter(([, v]) => !v.ok).map(([base, v]) => {
    const trueLit = v.sign === 'yes' ? `!${base}` : base
    const shownAt = facts.get(trueLit)
    const knowers = chars.filter(d => d.id !== c.id && now[d.id].get(base) && now[d.id].get(base)!.ok).map(d => d.id)
    return { who: c.id, base, v, shown: shownAt !== undefined && paraIdx(shownAt) <= i ? shownAt : null, knowers }
  }))
  const nested = nestedUpTo(report, i)
  const label = (base: string, gloss?: string) => atoms.get(base)?.label ?? gloss ?? base
  const att = (who: string, base: string) => ex.get(`${who}|${base}`)?.explain.at(-1)?.attitude ?? 'hard'
  return <div className="storyview minds">
    <svg width="0" height="0" style={{ position: 'absolute' }} aria-hidden="true"><defs>
      <pattern id="mhatch" width="4" height="4" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
        <rect width="4" height="4" className="hatch-bg" /><line x1="0" y1="0" x2="0" y2="4" className="hatch-ln" strokeWidth="2.2" /></pattern></defs></svg>
    <section>
      <h3>Who believes what, after ¶ {report.paragraphs[i]?.name ?? 'start'}</h3>
      <div className="row dim">Each cell: what the character thinks; ≠ and an outline when the world says otherwise ("actually"). Solid: held outright; lighter: provisional; faint: only noted. Click a cell for its sources.</div>
      <label className="row"><input type="checkbox" checked={onlyFalse} onChange={e => setOnlyFalse(e.target.checked)} /> only propositions someone is wrong about</label>
      <div className="mtable" style={{ ['--n' as string]: chars.length }}>
        <div className="mh" />{chars.map(c => <div key={c.id} className="mh" data-target={`char:${c.id}`} style={{ color: charColour(report, c.id) }}>{c.name}</div>)}
        <div className="mh dim">world</div>
        {tableRows.map(r => <React.Fragment key={r.base}>
          <div className="ml" data-target={atoms.has(r.base) ? `fact:${r.base}` : undefined}>{r.label}</div>
          {chars.map(c => {
            const v = now[c.id].get(r.base)
            if (!v) return <div key={c.id} className="mc none" title="no view">·</div>
            const wrong = !v.ok
            return <button key={c.id} className={`mc att-${att(c.id, r.base)} ${wrong ? 'wrong' : ''} ${cell?.who === c.id && cell.base === r.base ? 'sel' : ''}`}
              data-target={`belief:${c.id}:${r.base}`} onClick={() => setCell({ who: c.id, base: r.base })}>
              {wrong ? <><span className="ne">≠</span> thinks {v.sign === 'yes' ? 'so' : 'not'}<br /><span className="act">actually {v.sign === 'yes' ? 'not' : 'so'}</span></>
                : v.sign === 'yes' ? '✓ so' : '✗ not'}
            </button>
          })}
          <div className="mc world">{r.truth === null ? '?' : r.truth ? 'true' : 'false'}</div>
        </React.Fragment>)}
      </div>
      {cell && <Sources report={report} who={cell.who} base={cell.base} i={i} onClose={() => setCell(null)} />}
    </section>

    <section>
      <h3>Dramatic irony after ¶ {report.paragraphs[i]?.name ?? 'start'}</h3>
      {irony.length === 0 ? <div className="row dim">Nobody holds a false belief here.</div> :
        <ul className="irony">{irony.map(x => <li key={x.who + x.base} data-target={`belief:${x.who}:${x.base}`}>
          <b style={{ color: charColour(report, x.who) }}>{charName(report, x.who)}</b> thinks {x.v.sign === 'yes' ? '' : 'not: '}<i>{label(x.base, x.v.gloss)}</i>
          <span className="ne"> ≠ </span>actually {x.v.sign === 'yes' ? 'not' : 'so'}.
          <span className="dim"> {x.shown ? `The reader was shown the truth in ¶${x.shown}.` : 'The world holds the truth; the prose has not stated it yet.'}
            {x.knowers.length > 0 && ` ${x.knowers.map(k => charName(report, k)).join(' and ')} know${x.knowers.length > 1 ? '' : 's'}.`}</span></li>)}</ul>}
    </section>

    <section>
      <h3>Through their eyes
        <select value={eyes} onChange={e => setEyes(e.target.value)} aria-label="whose eyes">
          <option value="">choose a character</option>{chars.map(c => <option key={c.id} value={c.id}>{c.name}</option>)}</select></h3>
      {!eyes ? <div className="row dim">What one character thinks the others think, by ¶ {report.paragraphs[i]?.name ?? 'start'}: A → B → what B is thought to believe, marked wrong when B does not.</div> :
        (() => {
          const mine = nested.filter(n => n.who === eyes)
          if (!mine.length) return <div className="row dim">{charName(report, eyes)} has no beliefs about others' beliefs yet.</div>
          return chars.filter(c => c.id !== eyes).map(c => {
            const xs = mine.filter(n => n.about === c.id)
            if (!xs.length) return null
            return <div key={c.id} className="eyes">
              {xs.map((n, k) => <div key={k} className={`chainrow ${n.accurate ? '' : 'wrong'}`} data-target={`nested:${n.who}:${n.about}:${baseOf(n.lit)}`}>
                <span className="cchip" style={{ color: charColour(report, n.who) }}>{charName(report, n.who)}</span><span className="arr">→</span>
                <span className="cchip" style={{ color: charColour(report, n.about) }}>{charName(report, n.about)}</span><span className="arr">→</span>
                <span className="cchip prop">{n.gloss}</span>
                {!n.accurate && <span className="fb">wrong: {charName(report, n.about)} does not think so</span>}
                <span className="dim"> ¶{n.para}</span></div>)}
            </div>
          })
        })()}
    </section>

    <section>
      <h3>Beliefs over the story</h3>
      <div className="row dim">One lane per character; a bar per belief across the paragraphs that hold it; hatched where it is false; the line marks ¶ {report.paragraphs[i]?.name ?? 'start'}.</div>
      {chars.map(c => <Lanes key={c.id} report={report} who={c.id} views={views} current={i} label={label} />)}
    </section>
  </div>
}

function Lanes({ report, who, views, current, label }: {
  report: Report; who: string; views: ReturnType<typeof viewsOver>; current: number; label: (b: string, g?: string) => string
}) {
  const bases: string[] = []
  const gloss = new Map<string, string>()
  for (const v of views) for (const [b, x] of v[who]) { if (!bases.includes(b)) bases.push(b); gloss.set(b, x.gloss) }
  const nFalse = bases.filter(b => views.some(v => v[who].get(b) && !v[who].get(b)!.ok)).length
  const N = views.length
  if (!bases.length) return null
  return <details className="lanes" open={nFalse > 0 && bases.length <= 14}>
    <summary data-target={`char:${who}`}><b style={{ color: charColour(report, who) }}>{charName(report, who)}</b> <span className="dim">{bases.length} beliefs{nFalse ? `, ${nFalse} false at some point` : ''}</span></summary>
    <div className="lanegrid">
      {bases.map(b => <React.Fragment key={b}>
        <div className="ll" data-target={`belief:${who}:${b}`}>{label(b, gloss.get(b))}</div>
        <svg className="lb" viewBox={`0 0 ${N * 10} 10`} preserveAspectRatio="none" aria-label={`${label(b)} over the paragraphs`}>
          {views.map((v, k) => {
            const x = v[who].get(b)
            if (!x) return null
            return <rect key={k} x={k * 10} y={x.sign === 'yes' ? 1 : 3} width={10.4} height={x.sign === 'yes' ? 8 : 4}
              className={`lbar ${x.ok ? '' : 'false'}`} style={{ ['--lc' as string]: charColour(report, who) }}>
              <title>{`${k === 0 ? 'start' : `¶${report.paragraphs[k - 1].name}`}: ${x.sign === 'yes' ? 'thinks so' : 'thinks not'}${x.ok ? '' : ' (false)'}`}</title></rect>
          })}
          <line x1={(current + 1) * 10 + 5} x2={(current + 1) * 10 + 5} y1={0} y2={10} className="lcur" />
        </svg>
      </React.Fragment>)}
    </div>
  </details>
}
