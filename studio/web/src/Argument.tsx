import React, { useMemo, useState } from 'react'
import type { Argument, Report } from './types'
import { charColour, charName } from './Logic'
import { ArgTreeView, NodeBox, reinstated, treeOf, type TEdge, type TNode } from './ArgTree'

/** The story as an argument graph (Complete.lean `argumentGraph`; Dung, with
 *  the grounded labelling: facts are IN, what a fact attacks is OUT). Each
 *  belief opens into its tree: what supports it (being told, seeing, a
 *  connective) and what attacks it (the fact that contradicts it, a later
 *  belief that revises it). Defeated beliefs first. docs/ui-visualisation.md §8. */

type ANode = Argument['nodes'][number]

function index(report: Report, g: Argument) {
  const nodes = new Map(g.nodes.map(n => [n.id, n]))
  const into = new Map<string, { src: string; e: TEdge }[]>()
  for (const e of g.edges) {
    if (!into.has(e.tgt)) into.set(e.tgt, [])
    into.get(e.tgt)!.push({ src: e.src, e: { kind: e.kind, why: e.why } })
  }
  const attackers = (id: string) => (into.get(id) ?? []).filter(x => x.e.kind === 'attack').map(x => x.src)
  const label = (id: string) => nodes.get(id)?.status as 'in' | 'out' | undefined
  const name = (id: string) => { const n = nodes.get(id); return n ? `“${n.gloss}”` : id }
  const toNode = (n: ANode): TNode => ({
    id: n.id, label: n.status, text: n.gloss,
    kind: `${n.kind === 'fact' ? 'fact' : n.kind === 'said' ? `${charName(report, n.who)} says` : `${charName(report, n.who)} believes`} · ¶${n.para}`,
    sub: [n.note, reinstated(n.id, label, attackers, name)].filter(Boolean).join(' · ') || undefined,
    colour: n.kind === 'fact' ? undefined : charColour(report, n.who),
    target: [`arg:${n.id}`, ...(n.ats ?? []).map(String)].join(' '),
    title: n.lit,
  })
  return { nodes, into, toNode, tree: (id: string) => treeOf(id, nodes, x => into.get(x) ?? [], toNode) }
}

function Root({ id, ix }: { id: string; ix: ReturnType<typeof index> }) {
  const [open, setOpen] = useState(false)
  const n = ix.nodes.get(id)!
  const t = open ? ix.tree(id) : null
  return <div className="claimrow">
    {t ? <><button className="btn small" onClick={() => setOpen(false)}>close</button><ArgTreeView t={t} /></>
      : <NodeBox n={ix.toNode(n)} count={ix.into.get(id)?.length ?? 0} open={false} onClick={() => setOpen(true)} />}
  </div>
}

export function ArgumentView({ report }: { report: Report; onSelect?: (i: number) => void }) {
  const g = report.argument
  const ix = useMemo(() => g ? index(report, g) : null, [g, report])
  if (!g || !ix) return <div className="row dim">no argument graph for this story</div>
  const beliefs = g.nodes.filter(n => n.kind === 'belief')
  const outs = beliefs.filter(n => n.status === 'out')
  const byWho = report.characters.map(c => [c.id, beliefs.filter(n => n.who === c.id && n.status === 'in' && (ix.into.get(n.id)?.length ?? 0) > 0)] as const)
  return (
    <div className="storyview argpaper">
      <section>
        <h3>The story's argument</h3>
        <div className="row">{g.nodes.length} arguments · {g.edges.filter(e => e.kind === 'support').length} supports · <span className="bad">{g.edges.filter(e => e.kind === 'attack').length} attacks</span> · {outs.length} defeated</div>
        <div className="row dim">Grounded labelling: a fact the story asserts is IN; what it attacks is OUT. Click a belief for what supports and attacks it; right-click to inspect.</div>
      </section>
      {outs.length > 0 && <section><h4>Defeated (OUT): false or revised beliefs · {outs.length}</h4>
        {outs.map(n => <Root key={n.id} id={n.id} ix={ix} />)}</section>}
      {byWho.map(([who, ns]) => ns.length > 0 && <section key={who}>
        <h4><span style={{ color: charColour(report, who) }}>{charName(report, who)}</span>: beliefs that stand, with their grounds · {ns.length}</h4>
        {ns.map(n => <Root key={n.id} id={n.id} ix={ix} />)}</section>)}
    </div>
  )
}

export function argNodeInfo(report: Report, id: string) {
  const g = report.argument
  const n = g?.nodes.find(x => x.id === id)
  if (!g || !n) return null
  const ix = index(report, g)
  return { n, tree: ix.tree(id), inn: g.edges.filter(e => e.tgt === id), out: g.edges.filter(e => e.src === id), name: (x: string) => ix.nodes.get(x)?.gloss ?? x }
}
