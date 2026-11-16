import React, { useEffect, useMemo, useRef, useState } from 'react'
import type { Paper, PaperArg, PaperArgNode } from './types'
import { ArgTreeView, NodeBox, reinstated, treeOf, type TEdge, type TNode } from './ArgTree'
import { StyleView } from './Style'
import { ContextMenu, targetsAt, type Menu, type MenuItem } from './Inspector'

/** A paper read as an argument (World/Argument, `langlib argument`): the
 *  text on the left, on the right its claims grouped by how the reader ends
 *  up holding them, each opening into its tree of support and attack, the
 *  moves of each paragraph, its promises and what paid them, and its
 *  academic style. docs/ui-visualisation.md §8. */

const KIND: Record<string, string> = {
  claim: 'claim', definition: 'definition', lore: 'background', term: 'term', cite: 'cites prior work',
  example: 'worked example', evaluate: 'measured', deny: 'the authors deny', concede: 'the authors concede',
  promise: 'promise', contribution: 'contribution', hedge: 'hedge', deliver: 'delivers',
}
const pretty = (t: string) => t.replace(/_/g, ' ')

function supportLines(n: PaperArgNode) {
  return n.support.map(s => typeof s === 'string' ? s
    : `${s.for ? '' : 'against: '}${s.src}, ${s.reasons.join(', ')} = ${s.strength} (${s.attitude === 'radical' ? 'held outright' : s.attitude === 'conservative' ? 'held provisionally' : s.attitude})`)
}

export function argIndex(g: PaperArg) {
  const nodes = new Map(g.nodes.map(n => [n.id, n]))
  const into = new Map<string, { src: string; e: TEdge }[]>()
  for (const e of g.edges) {
    if (e.kind !== 'support' && e.kind !== 'attack') continue
    if (!into.has(e.tgt)) into.set(e.tgt, [])
    into.get(e.tgt)!.push({ src: e.src, e: { kind: e.kind, why: e.why } })
  }
  const label = (id: string) => nodes.get(id)?.label
  const attackers = (id: string) => (into.get(id) ?? []).filter(x => x.e.kind === 'attack').map(x => x.src)
  const name = (id: string) => { const n = nodes.get(id); return n ? `${KIND[n.kind] ?? n.kind} “${pretty(n.t)}”` : id }
  const toNode = (n: PaperArgNode): TNode => {
    const re = reinstated(n.id, label, attackers, name)
    const held = n.held === 'accepted' ? 'the reader accepts it' : n.held === "authors' word" ? "held on the authors' word only"
      : n.held === 'denied' ? 'the reader holds it false' : n.held === 'known' ? 'known' : ''
    return {
      id: n.id, label: n.label, kind: `${KIND[n.kind] ?? n.kind} · ¶${n.para}`, text: pretty(n.t),
      sub: [held, n.note, re].filter(Boolean).join(' · ') || undefined,
      target: `arg:${n.id}`, title: supportLines(n).join('\n') || undefined,
    }
  }
  return { nodes, into, toNode, tree: (id: string) => treeOf(id, nodes, x => into.get(x) ?? [], toNode) }
}

function ClaimRow({ id, ix, current }: { id: string; ix: ReturnType<typeof argIndex>; current: string }) {
  const [open, setOpen] = useState(false)
  const n = ix.nodes.get(id)!
  const kids = ix.into.get(id)?.length ?? 0
  const t = open ? ix.tree(id) : null
  return <div className={`claimrow ${n.para === current ? 'here' : ''}`}>
    {t ? <><button className="btn small" onClick={() => setOpen(false)}>close</button><ArgTreeView t={t} /></>
      : <NodeBox n={ix.toNode(n)} count={kids} open={false} onClick={() => setOpen(true)} />}
  </div>
}

export function PaperArgView({ paper, current }: { paper: Paper; current: number }) {
  const g = paper.argument
  const ix = useMemo(() => g && !g.error ? argIndex(g) : null, [g])
  const [upto, setUpto] = useState(false)
  if (!g || g.error || !ix) return <div className="storyview bad">{g?.error ?? 'no argument'}</div>
  const cur = paper.paragraphs[current]?.name ?? ''
  const shown = (n: PaperArgNode) => !upto || n.para <= cur
  const claims = g.nodes.filter(n => n.id.startsWith('P:') && n.kind === 'claim' && shown(n))
  const gapT = new Set(g.gaps.filter(x => x.kind === 'unsupported').map(x => x.t))
  const groups: [string, string, PaperArgNode[]][] = [
    ['out', 'Defeated (OUT): denied or conceded', claims.filter(n => n.label === 'out')],
    ['gap', 'Unsupported at the end of the excerpt', claims.filter(n => n.label !== 'out' && gapT.has(n.t))],
    ['word', "On the authors' word only (support deferred)", claims.filter(n => n.label !== 'out' && !gapT.has(n.t) && n.held !== 'accepted')],
    ['acc', 'Accepted by the reader', claims.filter(n => n.label !== 'out' && !gapT.has(n.t) && n.held === 'accepted')],
  ]
  const promises = g.nodes.filter(n => ['promise', 'contribution', 'hedge'].includes(n.kind) && shown(n))
  const paidBy = (id: string) => g.edges.find(e => e.kind === 'delivers' && e.src === id)
  return (
    <div className="storyview argpaper">
      <section>
        <h3>Argument <span className={`badge ${g.coherent ? 'valid' : g.valid ? 'plausible' : 'failing'}`}>{g.coherent ? 'coherent' : g.valid ? 'valid, with gaps' : 'invalid'}</span>
          {paper.proved && <span className="badge lean ok" title="Argument.lean proves these gaps, antitheses, contrasts and deferrals by decide +kernel">⊢ gaps proved</span>}</h3>
        {g.failure && <div className="row bad">move {g.failure.i}: {g.failure.why}</div>}
        <div className="row">{claims.length} claims · {g.edges.filter(e => e.kind === 'support').length} supports · <span className="bad">{g.edges.filter(e => e.kind === 'attack').length} attacks</span> · {g.gaps.length} gaps · {g.deferred.length} deferred</div>
        <div className="row dim">Grounded labelling: IN when every attacker is OUT, OUT when an attacker is IN. Click a claim for what supports and attacks it; right-click to inspect.</div>
        <label className="row"><input type="checkbox" checked={upto} onChange={e => setUpto(e.target.checked)} /> only what the reader has met by ¶ {cur}</label>
      </section>
      {groups.map(([k, title, ns]) => ns.length > 0 && <section key={k}>
        <h4>{title} · {ns.length}</h4>
        {ns.map(n => <ClaimRow key={n.id} id={n.id} ix={ix} current={cur} />)}
      </section>)}
      <section>
        <h4>Promises, hedges and what paid them</h4>
        <ul className="promises">{promises.map(n => {
          const d = paidBy(n.id)
          const at = d ? ix.nodes.get(d.tgt) : undefined
          return <li key={n.id} data-target={`arg:${n.id}`} className={d ? 'ok' : n.note.startsWith('never') ? 'bad' : 'dim'}>
            <span className="tn-kind">{KIND[n.kind]} · ¶{n.para}</span> {pretty(n.t)}
            <span> → {d ? <>{at?.kind === 'evaluate' ? 'measured' : 'delivered'} in ¶{at?.para}</> : n.note}</span></li>
        })}</ul>
      </section>
      {(g.antitheses.length > 0 || g.contrasts.length > 0) && <section>
        <h4>Denials</h4>
        {g.antitheses.map(t => <div key={t} className="row warn">antithesis: “{pretty(t)}” is denied though nobody put it forward</div>)}
        {[...new Set(g.contrasts)].map(t => <div key={t} className="row">contrast: denies “{pretty(t)}”, which was put forward</div>)}
      </section>}
    </div>
  )
}

const MOVE: Record<string, string> = { ...KIND, claim: 'claims', define: 'defines', motivate: 'motivates', example: 'works an example of', cite: 'cites for', contrast: 'contrasts', promise: 'promises', contribute: 'contributes', deliver: 'delivers', concede: 'concedes', deny: 'denies', hedge: 'hedges on', infer: 'infers', evaluate: 'measures', heading: 'section' }

export function PaperMoves({ paper, current, onSelect }: { paper: Paper; current: number; onSelect: (i: number) => void }) {
  const ref = useRef<HTMLDivElement>(null)
  useEffect(() => {
    const el = ref.current?.querySelector<HTMLElement>(`[data-card="${current}"]`)
    if (el && ref.current) ref.current.scrollTo({ top: el.offsetTop - 12, behavior: matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth' })
  }, [current])
  const g = paper.argument
  return <div className="logic" ref={ref}><div className="papermoves">
    {(g?.paragraphs ?? []).map((p, i) => <div key={p.name} className={`lcard ${i === current ? 'current' : ''} ${p.moves.some(m => !m.ok) ? 'v-failing' : 'v-valid'}`}
      data-card={i} data-para-name={p.name} onClick={() => onSelect(i)}>
      <div className="lc-head"><span className="pn">¶ {p.name}</span></div>
      <ul className="evs">{p.moves.map(m => <li key={m.i} className={`ev st-${m.ok ? 'yes' : 'no'}`}
        data-target={m.t ? `arg:P:${m.t}` : undefined}>
        <span className="st">{m.ok ? '●' : '✕'}</span>
        <span className="g">{MOVE[m.move] ?? m.move} {m.move === 'heading' ? m.sec : m.move === 'contrast' ? `${pretty(m.a ?? '')} with ${pretty(m.b ?? '')}` : <b>{pretty(m.t ?? '')}</b>}
          {m.premises && m.premises.length > 0 && <span className="dim"> because {m.premises.map(pretty).join(', ')}</span>}
          {m.sec !== undefined && m.move !== 'heading' && <span className="dim"> ({m.sec ? `section ${m.sec}` : 'later'})</span>}</span>
        {!m.ok && <div className="why">{m.why}</div>}
      </li>)}</ul>
    </div>)}
  </div></div>
}

/** Inspector for a paper's node: what it is, how the reader holds it and why, what it touches. */
export function PaperInspector({ paper, id }: { paper: Paper; id: string | null }) {
  const g = paper.argument
  if (!id) return <div className="storyview dim">Right-click a claim, move or promise and choose Inspect.</div>
  const n = g.nodes.find(x => x.id === id)
  if (!n) return <div className="storyview dim">That node is gone (the reading changed).</div>
  const ix = argIndex(g)
  const out = g.edges.filter(e => e.src === id), inn = g.edges.filter(e => e.tgt === id)
  const nm = (x: string) => { const m = ix.nodes.get(x); return m ? `${KIND[m.kind] ?? m.kind} “${pretty(m.t)}” (¶${m.para})` : x }
  const t = ix.tree(id)
  return <div className="inspector">
    <h3>{pretty(n.t)} <span className="dim">{KIND[n.kind] ?? n.kind} · ¶{n.para} · {n.voice}</span></h3>
    <section>
      <div className="ins-row"><span className="k">label</span><span>{n.label.toUpperCase()}</span></div>
      {n.held && <div className="ins-row"><span className="k">the reader</span><span>{n.held}</span></div>}
      {n.note && <div className="ins-row"><span className="k">note</span><span>{n.note}</span></div>}
      {n.support.length > 0 && <div className="ins-row"><span className="k">why held</span><ul className="ins-list">{supportLines(n).map((s, i) => <li key={i}>{s}</li>)}</ul></div>}
      {inn.length > 0 && <div className="ins-row"><span className="k">from</span><ul className="ins-list">{inn.map((e, i) => <li key={i}>{e.kind}: {nm(e.src)}{e.why ? ` (${e.why})` : ''}</li>)}</ul></div>}
      {out.length > 0 && <div className="ins-row"><span className="k">to</span><ul className="ins-list">{out.map((e, i) => <li key={i}>{e.kind}: {nm(e.tgt)}{e.why ? ` (${e.why})` : ''}</li>)}</ul></div>}
    </section>
    {t && t.kids.length > 0 && <section><h4>Its tree</h4><ArgTreeView t={t} openDepth={3} /></section>}
  </div>
}

type PTab = 'argument' | 'moves' | 'style' | 'inspect'

/** The two panels for a paper, under the Studio's top bar. */
export function PaperMain({ name, size, face }: { name: string; size: string; face: string }) {
  const [paper, setPaper] = useState<Paper | null>(null)
  const [tab, setTab] = useState<PTab>(() => (new URLSearchParams(location.search).get('ptab') as PTab) || 'argument')
  const [current, setCurrent] = useState(0)
  const [menu, setMenu] = useState<Menu | null>(null)
  const [inspecting, setInspecting] = useState<string | null>(null)
  const prose = useRef<HTMLDivElement>(null)
  const load = () => fetch(`/api/paper/${name}`).then(r => r.json()).then(setPaper).catch(() => {})
  useEffect(() => { setPaper(null); load() }, [name])
  useEffect(() => {
    if (new URLSearchParams(location.search).has('static')) return
    const es = new EventSource('/api/events')
    es.onmessage = m => { const msg = JSON.parse(m.data); if (msg.type === 'paper' && msg.paper === name) load() }
    return () => es.close()
  }, [name])
  useEffect(() => {
    const pane = prose.current
    if (!pane) return
    const onScroll = () => {
      const line = pane.getBoundingClientRect().top + pane.clientHeight * 0.4
      let best = 0
      for (const p of pane.querySelectorAll<HTMLElement>('[data-para]')) if (p.getBoundingClientRect().top <= line) best = Number(p.dataset.para)
      setCurrent(best)
    }
    pane.addEventListener('scroll', onScroll, { passive: true })
    onScroll()
    return () => pane.removeEventListener('scroll', onScroll)
  }, [paper])
  const select = (i: number) => {
    setCurrent(i)
    const el = prose.current?.querySelector<HTMLElement>(`[data-para="${i}"]`)
    if (el && prose.current) prose.current.scrollTo({ top: el.offsetTop - prose.current.clientHeight * 0.3, behavior: 'smooth' })
  }
  const onContextMenu = (e: React.MouseEvent) => {
    if (!paper) return
    const targets = targetsAt(e.target as HTMLElement)
    const items: MenuItem[] = []
    for (const t of targets) {
      const [kind, ...rest] = t.split(':')
      const key = rest.join(':')
      if (kind === 'arg') {
        const n = paper.argument.nodes.find(x => x.id === key)
        if (n) items.push({ label: `Inspect ${KIND[n.kind] ?? n.kind} “${pretty(n.t)}”`, run: () => { setInspecting(key); setTab('inspect') } })
      } else if (kind === 'para') {
        items.push({ label: `Show ¶ ${key}'s moves`, run: () => { setTab('moves'); select(Math.max(0, paper.paragraphs.findIndex(p => p.name === key))) } })
      }
    }
    if (!items.length) return
    e.preventDefault()
    setMenu({ x: e.clientX, y: e.clientY, items })
  }
  if (!paper) return <div className="main"><div className="prose-pane"><div className="prose"><p className="para empty">Reading the paper…</p></div></div></div>
  if (paper.error) return <div className="main"><div className="prose-pane"><div className="prose"><p className="para empty">{paper.error}</p></div></div></div>
  return (
    <div className="main" onContextMenu={onContextMenu}>
      <div className="prose-pane" ref={prose}>
        <article className={`prose overview ${face === 'sans' ? 'sans' : ''}`} style={{ ['--size' as string]: `${size}px` }}>
          <h1>{paper.title}</h1>
          {paper.paragraphs.map((p, i) => <p key={p.name} className={`para ${i === current ? 'current' : ''}`} data-para={i} data-para-name={p.name}
            onClick={() => setCurrent(i)}><span className="gutter"><span className="num">{p.name}</span></span>{p.text}</p>)}
        </article>
      </div>
      <aside className="right">
        <nav className="tabs">{(['argument', 'moves', 'style', ...(inspecting ? ['inspect'] : [])] as PTab[]).map(t =>
          <button key={t} className={tab === t ? 'on' : ''} onClick={() => setTab(t)}>{t}</button>)}</nav>
        {tab === 'argument' && <div className="logic"><PaperArgView paper={paper} current={current} /></div>}
        {tab === 'moves' && <PaperMoves paper={paper} current={current} onSelect={select} />}
        {tab === 'style' && <div className="logic"><StyleView reports={[['academic', paper.academic]]} /></div>}
        {tab === 'inspect' && <div className="logic"><PaperInspector paper={paper} id={inspecting} /></div>}
      </aside>
      {menu && <ContextMenu menu={menu} onClose={() => setMenu(null)} />}
    </div>
  )
}
