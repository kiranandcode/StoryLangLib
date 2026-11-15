import React, { useMemo, useState } from 'react'
import type { Report } from './types'
import { charColour, charName } from './Logic'

/** The story as an argument graph (Dung; ASPIC+ and Carneades for the structure): the facts it
 *  asserts, the beliefs it gives its characters and what is said, with support and attack edges.
 *  Lanes are the world and each character; columns are paragraphs. Grounded labelling: a fact is
 *  in, what a fact attacks is out. */
export function ArgumentView({ report, onSelect }: { report: Report; onSelect: (i: number) => void }) {
  const g = report.argument
  const [hover, setHover] = useState<string | null>(null)
  const layout = useMemo(() => {
    if (!g) return null
    const paras = report.paragraphs.map(p => p.name)
    const who = [...new Set(g.nodes.filter(n => n.kind !== 'fact').map(n => n.who))]
    const lanes = ['', ...report.characters.map(c => c.id).filter(c => who.includes(c))]
    const LABEL = 66, COL = 132, NH = 20, GAP = 5, PADT = 26
    // stack the nodes of each (lane, paragraph) cell
    const cells = new Map<string, number>()
    const laneRows = new Map<string, number>()
    const place = new Map<string, { x: number; row: number; lane: string; w: number }>()
    for (const n of g.nodes) {
      const lane = n.kind === 'fact' ? '' : n.who
      const key = `${lane}|${n.para}`
      const row = cells.get(key) ?? 0
      cells.set(key, row + 1)
      laneRows.set(lane, Math.max(laneRows.get(lane) ?? 1, row + 1))
      const col = Math.max(0, paras.indexOf(n.para))
      place.set(n.id, { x: LABEL + col * COL + COL / 2, row, lane, w: Math.min(COL - 10, n.lit.length * 6.2 + 16) })
    }
    const laneTop = new Map<string, number>()
    let y = PADT
    for (const l of lanes) { laneTop.set(l, y); y += (laneRows.get(l) ?? 1) * (NH + GAP) + 14 }
    const pos = (id: string) => {
      const p = place.get(id)!
      return { x: p.x, y: laneTop.get(p.lane)! + p.row * (NH + GAP) + NH / 2, w: p.w }
    }
    return { paras, lanes, laneTop, laneRows, pos, width: LABEL + paras.length * COL + 8, height: y + 4, LABEL, COL, NH, GAP, PADT }
  }, [g, report])
  if (!g || !layout) return <div className="row dim">no argument graph for this story</div>
  const { paras, lanes, laneTop, laneRows, pos, width, height, LABEL, COL, NH, GAP, PADT } = layout
  const near = (id: string) => hover === null || hover === id ||
    g.edges.some(e => (e.src === hover && e.tgt === id) || (e.tgt === hover && e.src === id))
  const outs = g.nodes.filter(n => n.status === 'out')
  return (
    <div className="argview">
      <div className="row">{g.nodes.length} arguments · {g.edges.filter(e => e.kind === 'support').length} supports · <span className="bad">{g.edges.filter(e => e.kind === 'attack').length} attacks</span>
        {outs.length > 0 && <> · out (defeated): {outs.map(n => `${charName(report, n.who)}: ${n.lit}`).join(', ')}</>}</div>
      <div className="arg-wrap">
        <svg className="arg" width={width} height={height}>
          <defs>
            <marker id="argsup" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto"><path d="M0,0 L8,4 L0,8 z" className="argsup-head" /></marker>
            <marker id="argatt" viewBox="0 0 6 10" refX="5" refY="5" markerWidth="6" markerHeight="10" orient="auto"><path d="M5,0 L5,10" className="argatt-head" /></marker>
          </defs>
          {paras.map((p, k) => <g key={p}>
            <line x1={LABEL + k * COL} x2={LABEL + k * COL} y1={PADT - 8} y2={height} className="argcol" />
            <text x={LABEL + k * COL + COL / 2} y={14} textAnchor="middle" className="argpara"
              onClick={() => onSelect(k)}>¶ {p}</text>
          </g>)}
          {lanes.map(l => <g key={l || 'world'}>
            <rect x={0} y={laneTop.get(l)! - 6} width={width} height={(laneRows.get(l) ?? 1) * (NH + GAP) + 6}
              className={`arglane ${l ? '' : 'world'}`} />
            <text x={6} y={laneTop.get(l)! + NH / 2 + 4} className="arglanel"
              style={{ fill: l ? charColour(report, l) : undefined }}>{l ? charName(report, l) : 'the world'}</text>
          </g>)}
          {g.edges.map((e, k) => {
            const a = pos(e.src), b = pos(e.tgt)
            const right = b.x >= a.x
            const x1 = right ? a.x + a.w / 2 : a.x - a.w / 2, x2 = b.x === a.x ? b.x + b.w / 2 : right ? b.x - b.w / 2 : b.x + b.w / 2
            const sameCol = Math.abs(b.x - a.x) < 1
            const d = sameCol
              ? `M ${a.x + a.w / 2} ${a.y} C ${a.x + a.w / 2 + 30} ${a.y}, ${b.x + b.w / 2 + 30} ${b.y}, ${b.x + b.w / 2} ${b.y}`
              : `M ${x1} ${a.y} C ${(x1 + x2) / 2} ${a.y}, ${(x1 + x2) / 2} ${b.y}, ${x2} ${b.y}`
            const lit = hover === null || hover === e.src || hover === e.tgt
            return <path key={k} d={d} className={`argedge ${e.kind} ${lit ? '' : 'faint'}`}
              markerEnd={`url(#${e.kind === 'attack' ? 'argatt' : 'argsup'})`}><title>{`${e.kind}: ${e.why}`}</title></path>
          })}
          {g.nodes.map(n => {
            const p = pos(n.id)
            return <g key={n.id} className={`argnode ${n.kind} ${n.status} ${near(n.id) ? '' : 'faint'}`}
              data-target={(n.ats ?? []).join(' ') || undefined}
              onMouseEnter={() => setHover(n.id)} onMouseLeave={() => setHover(null)}
              style={{ '--lc': n.kind === 'fact' ? 'var(--ink-2)' : charColour(report, n.who) } as React.CSSProperties}>
              <rect x={p.x - p.w / 2} y={p.y - NH / 2} width={p.w} height={NH} rx={n.kind === 'fact' ? 2 : 9} />
              <text x={p.x} y={p.y + 3.5} textAnchor="middle">{n.lit}</text>
              <title>{`${n.kind === 'fact' ? 'fact' : n.kind === 'said' ? `${charName(report, n.who)} says` : `${charName(report, n.who)} believes`}: ${n.gloss}` +
                `\n${n.status === 'in' ? 'in (undefeated)' : 'out (defeated)'}${n.note ? ` · ${n.note}` : ''}` +
                g.edges.filter(e => e.tgt === n.id).map(e => `\n${e.kind === 'attack' ? '⊣' : '←'} ${e.src.replace(/^[A-Z]:/, '')}: ${e.why}`).join('')}</title>
            </g>
          })}
        </svg>
      </div>
      <div className="row dim argkey">square: a fact · rounded: a belief (its character's colour) · dashed: what is said · grey arrow: support · red bar: attack · struck through: out (defeated). Hover a node for its supports and attackers.</div>
    </div>
  )
}
