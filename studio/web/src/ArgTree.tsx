import React, { useState } from 'react'

/** One argument and what bears on it, drawn top-down as an outline tree
 *  (docs/ui-visualisation.md §8): the conclusion first, its supporters and
 *  attackers below, theirs below them. A tree has no crossings and straight
 *  chains; nodes are HTML so their text wraps at any width. Each edge is a
 *  stub tapered from its source (the child) to its target (the parent);
 *  attacks are red and dashed as well. Labels are words first: IN, OUT, UNDEC. */

export type Label = 'in' | 'out' | 'undec'
export interface TNode {
  id: string
  label?: Label
  kind: string            // shown as a small tag: claim, cite, belief, said, ...
  text: React.ReactNode
  sub?: React.ReactNode   // a second line: how it is held, its note
  colour?: string         // a character's colour, for beliefs
  target?: string         // data-target for right-click inspect
  title?: string
  faint?: boolean
}
export interface TEdge { kind: 'support' | 'attack' | 'contrast' | 'delivers'; why: string }
export interface TTree { node: TNode; edge?: TEdge; kids: TTree[]; repeat?: boolean }

/** Build the tree of `root` from edges into each node; a node met again is a stub. */
export function treeOf<N>(root: string, nodes: Map<string, N>, edgesInto: (id: string) => { src: string; e: TEdge }[],
  toNode: (n: N) => TNode, depth = 4): TTree | null {
  const go = (id: string, seen: Set<string>, d: number, edge?: TEdge): TTree | null => {
    const n = nodes.get(id)
    if (!n) return null
    if (seen.has(id)) return { node: toNode(n), edge, kids: [], repeat: true }
    const s2 = new Set(seen).add(id)
    const kids = d <= 0 ? [] : edgesInto(id).map(x => go(x.src, s2, d - 1, x.e)).filter((t): t is TTree => !!t)
    // attackers first: what defeats a node is what the reader needs first
    kids.sort((a, b) => (a.edge?.kind === 'attack' ? 0 : 1) - (b.edge?.kind === 'attack' ? 0 : 1))
    return { node: toNode(n), edge, kids }
  }
  return go(root, new Set(), depth)
}

export function Badge({ label }: { label?: Label }) {
  if (!label) return null
  return <span className={`lab lab-${label}`} title={label === 'in' ? 'IN: every attacker is out' : label === 'out' ? 'OUT: an attacker is in' : 'UNDEC: undecided'}>
    {label.toUpperCase()}</span>
}

export function NodeBox({ n, onClick, open, count }: { n: TNode; onClick?: () => void; open?: boolean; count?: number }) {
  return (
    <div className={`tnode lab-${n.label ?? 'none'} ${n.faint ? 'faint' : ''}`} data-target={n.target} title={n.title}
      style={n.colour ? { ['--lc' as string]: n.colour } : undefined} onClick={onClick}>
      <div className="tn-head">
        <Badge label={n.label} />
        <span className="tn-kind">{n.kind}</span>
        {count !== undefined && count > 0 && <span className="tn-more">{open ? '▾' : '▸'} {count}</span>}
      </div>
      <div className="tn-text">{n.text}</div>
      {n.sub && <div className="tn-sub">{n.sub}</div>}
    </div>
  )
}

function Branch({ t, depth, openDepth }: { t: TTree; depth: number; openDepth: number }) {
  const [open, setOpen] = useState(depth < openDepth)
  const k = t.edge?.kind
  return (
    <li className={`tb ${k ? `e-${k}` : ''}`}>
      {k && <span className="stub" title={`${k}: ${t.edge!.why}`} aria-label={k} />}
      {k && <span className="ewhy">{k === 'attack' ? 'attacks' : k === 'support' ? 'supports' : k}{t.edge!.why ? `: ${t.edge!.why}` : ''}</span>}
      <NodeBox n={t.repeat ? { ...t.node, sub: <>{t.node.sub} <i>(shown above)</i></> } : t.node}
        count={t.kids.length} open={open} onClick={t.kids.length ? () => setOpen(!open) : undefined} />
      {open && t.kids.length > 0 && <ul className="tkids">{t.kids.map((c, i) => <Branch key={c.node.id + i} t={c} depth={depth + 1} openDepth={openDepth} />)}</ul>}
    </li>
  )
}

export function ArgTreeView({ t, openDepth = 2 }: { t: TTree; openDepth?: number }) {
  return <ul className="argtree"><Branch t={t} depth={0} openDepth={openDepth} /></ul>
}

/** Why a node is IN although attacked: every attacker is out (reinstatement, said on the node). */
export function reinstated(id: string, label: (id: string) => Label | undefined,
  attackers: (id: string) => string[], name: (id: string) => string): string {
  const as = attackers(id)
  if (label(id) !== 'in' || as.length === 0) return ''
  const by = as.map(a => attackers(a).find(x => label(x) === 'in')).filter(Boolean) as string[]
  return `reinstated: ${as.map(name).join(', ')} ${as.length > 1 ? 'are' : 'is'} out${by.length ? `, defeated by ${by.map(name).join(', ')}` : ''}`
}
