import React, { useLayoutEffect, useMemo, useRef, useState } from 'react'
import type { Paragraph, Report, Theorem } from './types'
import { entityColour } from './Prose'

const charColour = (report: Report, id: string) => {
  const i = report.characters.findIndex(c => c.id === id)
  return i >= 0 ? `var(--c${i % 6})` : 'var(--ink-3)'
}
const charName = (report: Report, id: string) => report.characters.find(c => c.id === id)?.name ?? id

/** Place order that minimises crossings of the storyline (exhaustive; stories have few places). */
function placeOrder(report: Report): string[] {
  const places = [...report.places]
  const rows = [report.startLine, ...report.storyline]
  const chars = report.characters.map(c => c.id)
  const perms = (xs: string[]): string[][] => xs.length <= 1 ? [xs] :
    xs.flatMap((x, i) => perms([...xs.slice(0, i), ...xs.slice(i + 1)]).map(p => [x, ...p]))
  let best = places, bestCost = Infinity
  for (const order of places.length <= 6 ? perms(places) : [places]) {
    const pos = (pl: string) => { const i = order.indexOf(pl); return i < 0 ? order.length : i }
    let cost = 0
    for (let k = 1; k < rows.length; k++)
      for (let a = 0; a < chars.length; a++) for (let b = a + 1; b < chars.length; b++) {
        const d0 = pos(rows[k - 1][chars[a]]?.place) - pos(rows[k - 1][chars[b]]?.place)
        const d1 = pos(rows[k][chars[a]]?.place) - pos(rows[k][chars[b]]?.place)
        if (d0 * d1 < 0) cost++
      }
    // prefer orders where places used earlier sit left, for stability
    if (cost < bestCost) { best = order; bestCost = cost }
  }
  return best
}

function Spine({ report, tops, height, current }: { report: Report; tops: number[]; height: number; current: number }) {
  const order = useMemo(() => placeOrder(report), [report])
  const cols = [...order, 'offstage']
  const colW = 20, pad = 10, lane = 4
  const width = pad * 2 + cols.length * colW
  const x = (place: string, ci: number, row: Record<string, { place: string }>) => {
    const col = Math.max(0, cols.indexOf(place))
    const here = report.characters.filter(c => row[c.id]?.place === place).map(c => c.id)
    const k = here.indexOf(report.characters[ci].id)
    return pad + col * colW + colW / 2 + (k - (here.length - 1) / 2) * lane
  }
  const rows = [report.startLine, ...report.storyline]
  const ys = [14, ...tops.map(t => t + 22)]
  return (
    <svg className="spine" width={width} height={Math.max(height, 40)} aria-label="storyline: where each character is after each paragraph">
      {cols.map((c, i) => (
        <g key={c}>
          <line x1={pad + i * colW + colW / 2} x2={pad + i * colW + colW / 2} y1={0} y2={height}
            className="col" />
          <text x={pad + i * colW + colW / 2} y={8} className="collabel" textAnchor="middle">{c === 'offstage' ? '…' : c.slice(0, 3)}</text>
        </g>
      ))}
      {current >= 0 && tops[current] !== undefined && (
        <rect x={0} y={tops[current]} width={width} height={(tops[current + 1] ?? height) - tops[current]} className="cur" />
      )}
      {report.characters.map((c, ci) => {
        let d = ''
        rows.forEach((row, k) => {
          const pl = row[c.id]?.place ?? 'offstage'
          const px = x(pl, ci, row), py = ys[k]
          if (k === 0) d += `M ${px} ${py}`
          else {
            const prev = rows[k - 1][c.id]?.place ?? 'offstage'
            const qx = x(prev, ci, rows[k - 1])
            const turn = Math.max(ys[k - 1] + 4, py - 18)
            d += ` L ${qx} ${turn} C ${qx} ${turn + 9}, ${px} ${py - 9}, ${px} ${py}`
          }
        })
        const last = rows[rows.length - 1][c.id]?.place ?? 'offstage'
        d += ` L ${x(last, ci, rows[rows.length - 1])} ${height}`
        return (
          <g key={c.id}>
            <path d={d} stroke={charColour(report, c.id)} className="line" />
            {rows.map((row, k) => {
              const pl = row[c.id]?.place ?? 'offstage'
              if (pl === 'offstage') return null
              return <circle key={k} cx={x(pl, ci, row)} cy={ys[k]} r={2.6}
                className={row[c.id]?.known ? 'known' : 'assumed'}
                style={{ stroke: charColour(report, c.id), fill: row[c.id]?.known ? charColour(report, c.id) : 'var(--panel)' }}>
                <title>{`${c.name}: ${pl}${row[c.id]?.known ? '' : ' (assumed)'}`}</title>
              </circle>
            })}
          </g>
        )
      })}
    </svg>
  )
}

function Lit({ s }: { s: string }) { return <code className="lit">{s}</code> }

function Section({ title, children }: { title: string; children: React.ReactNode }) {
  return <div className="sec"><div className="sec-t">{title}</div>{children}</div>
}

function Card({ report, p, index, current, theorems, onSelect }: {
  report: Report; p: Paragraph; index: number; current: boolean
  theorems: [string, Theorem][]; onSelect: (i: number) => void
}) {
  const [open, setOpen] = useState<Record<string, boolean>>({})
  const d = p.delta
  const proved = theorems.length > 0 && theorems.every(([, t]) => t.ok)
  const anyFailed = theorems.some(([, t]) => t.ok === false)
  const verdictText = p.verdict === 'valid' ? 'valid' : p.verdict === 'plausible' ? `plausible · ${p.assumptions.length} assumed` : 'failing'
  const times = p.events.map(e => e.time).filter((t): t is [number, number] => !!t)
  const t0 = Math.min(...times.map(t => t[0])), t1 = Math.max(...times.map(t => t[1]))
  return (
    <div className={`lcard ${current ? 'current' : ''} v-${p.verdict}`} data-card={index} data-para-name={p.name} onClick={() => onSelect(index)}>
      <div className="lc-head">
        <span className="pn">¶ {p.name}</span>
        {p.beat && <span className="beat">{p.beat}</span>}
        <span className="spacer" />
        <span className={`badge ${p.verdict}`}>{p.verdict === 'valid' ? '✓' : p.verdict === 'plausible' ? '◐' : '✕'} {verdictText}</span>
        {theorems.length > 0 && <span className={`badge lean ${proved ? 'ok' : anyFailed ? 'bad' : ''}`}
          title={theorems.map(([n, t]) => `${t.ok ? '✓' : t.ok === false ? '✕' : '…'} ${n}: ${t.statement}`).join('\n')}>
          {proved ? '⊢ proved' : anyFailed ? '⊬ proof failed' : '⊢ …'}</span>}
      </div>

      {p.freshness && (p.freshness.status === 'stale' || p.freshness.status === 'unstamped') && <Section title="reading">
        {p.freshness.status === 'stale'
          ? p.freshness.why.map((w, i) => <div key={i} className="row bad">stale: {w}</div>)
          : <div className="row warn">not stamped: these events may predate the current prose (no text_sha)</div>}
      </Section>}

      {p.events.length > 0 && <Section title="events">
        <ul className="evs">{p.events.map((e, i) => (
          <li key={i} className={`ev st-${e.status}`} data-target={`ev:${p.name}:${i}`}>
            <span className="st">{e.status === 'yes' ? '●' : e.status === 'unknown' ? '◐' : '✕'}</span>
            <span className="g">{e.gloss}{e.phase !== 'main' && <em className="phase"> {e.phase}</em>}</span>
            {e.unmotivated && <span className="flag" title={e.motive}>unmotivated</span>}
            {e.src !== 'plan' && <span className="src" title="read off the prose">¶</span>}
            {e.why && <div className="why">{e.why}</div>}
          </li>))}</ul>
      </Section>}

      {(d.moves.length > 0 || d.objects.length > 0) && <Section title="scene">
        {d.moves.map((m, i) => <div key={i} className="row"><b data-target={`char:${m.who}`} style={{ color: charColour(report, m.who) }}>{charName(report, m.who)}</b> {m.assumed ? <>assumed in the <b>{m.to}</b></> : <>{m.from === 'offstage' ? 'enters' : `${m.from} →`} <b>{m.to}</b></>}</div>)}
        {d.objects.map((o, i) => <div key={i} className="row">the {o.what}: {o.now.heldBy ? <>held by <b style={{ color: charColour(report, o.now.heldBy) }}>{charName(report, o.now.heldBy)}</b></> : <>in the <b>{o.now.place}</b></>}</div>)}
      </Section>}

      {(d.beliefs.some(b => !b.lit.startsWith('at(') || b.false) || d.nested.some(n => !n.lit.startsWith('at('))) && <Section title="beliefs">
        {d.beliefs.filter(b => !b.lit.startsWith('at(') || b.false).map((b, i) => {
          const key = `b${i}`
          return <div key={key} className={`belief ${b.change} ${b.false ? 'false' : ''}`} data-target={b.lit.includes('(') ? undefined : `fact:${b.lit.replace(/^!/, '')}`}>
            <button className="bl" onClick={e => { e.stopPropagation(); setOpen(o => ({ ...o, [key]: !o[key] })) }}>
              <span className="who" data-target={`char:${b.who}`} style={{ color: charColour(report, b.who) }}>{charName(report, b.who)}</span>
              <span className="chg">{b.change === 'gained' ? '+' : '−'}</span>
              <span>{b.gloss}</span>
              {b.false && <span className="fb" title="false belief">false</span>}
            </button>
            {open[key] && <ul className="explain">{b.explain.map((x, j) => (
              <li key={j}><Lit s={x.lit} /> from <b>{x.src}</b>: {x.reasons.map(([r, n]) => `${r} ${n >= 0 ? '+' : ''}${n}`).join(', ')} = {x.strength}; {x.attitude}; <i>{x.status}</i>{x.caught ? ' (caught out)' : ''}</li>))}</ul>}
          </div>
        })}
        {d.nested.filter(n => !n.lit.startsWith('at(')).map((n, i) => <div key={i} className="row nested"><span style={{ color: charColour(report, n.who) }}>{charName(report, n.who)}</span> thinks <span style={{ color: charColour(report, n.about) }}>{charName(report, n.about)}</span> thinks: {n.gloss}{!n.accurate && <span className="fb">wrong</span>}</div>)}
      </Section>}

      {(d.bonds.length > 0 || d.consentGiven.length > 0 || d.consentWithdrawn.length > 0) && <Section title="relationships & consent">
        <div className="chips">{d.bonds.map((b, i) => <span key={i} className={`chip ${b.after > b.before ? 'up' : 'down'}`} data-target={`bond:${b.from}>${b.to}`}>
          <span style={{ color: charColour(report, b.from) }}>{charName(report, b.from)}</span>→<span style={{ color: charColour(report, b.to) }}>{charName(report, b.to)}</span> {b.dim} {b.after > b.before ? '+' : '−'}{Math.abs(b.after - b.before)} <span className="dim">({b.after})</span></span>)}</div>
        {d.consentGiven.map((c, i) => <div key={i} className="row consent">✓ {c}</div>)}
        {d.consentWithdrawn.map((c, i) => <div key={i} className="row consent off">↺ {c} (withdrawn)</div>)}
      </Section>}

      {d.goals.length > 0 && <Section title="goals">
        {d.goals.map((g, i) => <div key={i} className="row"><span data-target={`char:${g.who}`} style={{ color: charColour(report, g.who) }}>{charName(report, g.who)}</span> wants <Lit s={g.goal} /></div>)}
      </Section>}

      {p.claims.length > 0 && <Section title="claims">
        {p.claims.map((c, i) => <div key={i} className={`row claim ${c.holds ? 'ok' : 'bad'}`}>{c.holds ? '⊨' : '⊭'} <Lit s={c.claim} />{c.error && <span className="why"> {c.error}</span>}</div>)}
      </Section>}

      {p.realisation && <Section title="plan → prose">
        <div className={`row ${p.realisation.realises ? 'ok' : 'bad'}`}>{p.realisation.realises ? 'the prose realises its plan' : 'the prose does not realise its plan'}</div>
        {p.realisation.missing.map((m, i) => <div key={i} className="row bad">missing <Lit s={m} /></div>)}
        {p.realisation.extra.map((m, i) => <div key={i} className="row warn">extra <Lit s={m} /></div>)}
      </Section>}

      {p.doc && !p.doc.check.ok && <Section title="annotation">
        {[...p.doc.check.edits, ...p.doc.check.refIssues].slice(0, 4).map((x, i) => <div key={i} className="row bad">{x}</div>)}
      </Section>}

      {times.length > 0 && <Section title="time">
        <svg className="mini-time" width="100%" height={8 + p.events.length * 7} viewBox={`0 0 200 ${8 + p.events.length * 7}`} preserveAspectRatio="none">
          {p.events.map((e, i) => e.time && (
            <rect key={i} x={((e.time[0] - t0) / Math.max(1, t1 - t0)) * 196 + 2} y={4 + i * 7}
              width={Math.max(3, ((e.time[1] - e.time[0]) / Math.max(1, t1 - t0)) * 196)} height={4} rx={1.5}
              className={`tbar ${e.phase}`}><title>{`${e.gloss}: [${e.time[0]}, ${e.time[1]}] min`}</title></rect>))}
        </svg>
        <div className="row dim">minutes {t0}–{t1} of story time{p.events.some(e => e.phase !== 'main') ? ` · ${[...new Set(p.events.map(e => e.phase).filter(x => x !== 'main'))].join(', ')}` : ''}</div>
      </Section>}

      {p.retro.length > 0 && <Section title="earlier paragraphs, revisited">
        {p.retro.map((r, i) => <div key={i} className="row warn">event {r.i}: {r.status} ({r.why})</div>)}
      </Section>}
    </div>
  )
}

export function LogicPanel({ report, current, onSelect, scrollRef }: {
  report: Report; current: number; onSelect: (i: number) => void
  scrollRef: React.RefObject<HTMLDivElement>
}) {
  const wrap = useRef<HTMLDivElement>(null)
  const [tops, setTops] = useState<number[]>([])
  const [height, setHeight] = useState(0)
  useLayoutEffect(() => {
    const el = wrap.current
    if (!el) return
    const measure = () => {
      const cards = [...el.querySelectorAll<HTMLElement>('[data-card]')]
      setTops(cards.map(c => c.offsetTop))
      setHeight(el.scrollHeight)
    }
    measure()
    const ro = new ResizeObserver(measure)
    ro.observe(el)
    el.querySelectorAll('[data-card]').forEach(c => ro.observe(c))
    return () => ro.disconnect()
  }, [report])
  const thms = Object.entries(report.proofs?.theorems ?? {})
  return (
    <div className="logic" ref={scrollRef}>
      <div className="cards" ref={wrap}>
        <Spine report={report} tops={tops} height={height} current={current} />
        <div className="startcard">
          <span className="pn">start</span>
          {report.characters.map(c => <span key={c.id} className="who" data-target={`char:${c.id}`} style={{ color: charColour(report, c.id) }}>
            {c.name}: {report.startLine[c.id]?.place ?? 'offstage'}</span>)}
        </div>
        {report.paragraphs.map((p, i) => (
          <Card key={p.name} report={report} p={p} index={i} current={i === current}
            theorems={thms.filter(([n]) => n.startsWith(`p${p.name}_`))} onSelect={onSelect} />
        ))}
      </div>
    </div>
  )
}

export { charColour, charName, entityColour }
