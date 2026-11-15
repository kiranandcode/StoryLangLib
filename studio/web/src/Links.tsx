import { useEffect, useState } from 'react'

/** Lines from what is hovered in the side panel to the words of the prose it is about.
 *  Anything in the right panel with a `data-target` ("tok:07:23", "ev:07:2", "char:hisoka", ...)
 *  is linked to the prose elements carrying the same key; those light up, and a curve is drawn
 *  from the hovered item to each one in view. Pointer-transparent; follows scrolling. */
type Line = { x1: number; y1: number; x2: number; y2: number }

export function LinkLines() {
  const [lines, setLines] = useState<Line[]>([])
  const [offscreen, setOffscreen] = useState<{ up: number; down: number; x: number }>({ up: 0, down: 0, x: 0 })
  useEffect(() => {
    let cur: Element | null = null
    let lit: Element[] = []
    const clear = () => { lit.forEach(e => e.classList.remove('linked')); lit = [] }
    const draw = () => {
      clear()
      if (!cur || !cur.isConnected) { setLines([]); setOffscreen({ up: 0, down: 0, x: 0 }); return }
      const keys = ((cur as HTMLElement).dataset?.target ?? cur.getAttribute('data-target') ?? '').split(/\s+/).filter(Boolean)
      const found = new Set<Element>()
      for (const k of keys) document.querySelectorAll(`.prose [data-target~="${CSS.escape(k)}"]`).forEach(e => found.add(e))
      const src = cur.getBoundingClientRect()
      const out: Line[] = []
      let up = 0, down = 0, minX = Infinity
      // one line per run of adjacent words (a phrase), to the end of its first visual line
      const els = [...found].sort((a, b) => a.compareDocumentPosition(b) & Node.DOCUMENT_POSITION_FOLLOWING ? -1 : 1)
      const runs: Element[][] = []
      for (const e of els) {
        e.classList.add('linked'); lit.push(e)
        const last = runs[runs.length - 1]?.slice(-1)[0]
        const i = Number((e as HTMLElement).dataset?.i), j = Number((last as HTMLElement | undefined)?.dataset?.i)
        if (last && last.parentElement === e.parentElement && Number.isFinite(i) && i === j + 1) runs[runs.length - 1].push(e)
        else runs.push([e])
      }
      for (const run of runs) {
        const r0 = run[0].getBoundingClientRect()
        if (r0.bottom < 0) { up++; continue }
        if (r0.top > window.innerHeight) { down++; continue }
        const sameLine = run.map(e => e.getBoundingClientRect()).filter(r => Math.abs(r.top - r0.top) < 4)
        const right = Math.max(...sameLine.map(r => r.right))
        minX = Math.min(minX, right)
        if (out.length < 40) out.push({ x1: src.left, y1: src.top + Math.min(src.height / 2, 11), x2: right + 2, y2: r0.top + r0.height / 2 })
      }
      setLines(out)
      setOffscreen({ up, down, x: Number.isFinite(minX) ? minX : window.innerWidth * 0.4 })
    }
    const onOver = (e: MouseEvent) => {
      const t = e.target as Element | null
      const el = t?.closest?.('.right [data-target]') ?? null
      if (el !== cur) { cur = el; draw() }
    }
    const onOut = (e: MouseEvent) => { if (!e.relatedTarget) { cur = null; draw() } }
    const onScroll = () => { if (cur) draw() }
    document.addEventListener('mouseover', onOver)
    document.addEventListener('mouseout', onOut)
    window.addEventListener('scroll', onScroll, true)
    window.addEventListener('resize', onScroll)
    return () => {
      clear()
      document.removeEventListener('mouseover', onOver)
      document.removeEventListener('mouseout', onOut)
      window.removeEventListener('scroll', onScroll, true)
      window.removeEventListener('resize', onScroll)
    }
  }, [])
  if (!lines.length && !offscreen.up && !offscreen.down) return null
  return (
    <svg className="linklines" width="100%" height="100%">
      {lines.map((l, k) => {
        const dx = Math.max(40, (l.x1 - l.x2) * 0.45)
        return <g key={k}>
          <path d={`M ${l.x1} ${l.y1} C ${l.x1 - dx} ${l.y1}, ${l.x2 + dx} ${l.y2}, ${l.x2} ${l.y2}`} />
          <circle cx={l.x2} cy={l.y2} r={2.6} />
        </g>
      })}
      {offscreen.up > 0 && <text x={offscreen.x} y={16} className="off">↑ {offscreen.up} above</text>}
      {offscreen.down > 0 && <text x={offscreen.x} y={window.innerHeight - 10} className="off">↓ {offscreen.down} below</text>}
    </svg>
  )
}
