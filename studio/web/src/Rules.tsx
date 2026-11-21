import React, { createContext, useCallback, useContext, useEffect, useMemo, useRef, useState } from 'react'
import './rules.css'

/** An argument's inferences as informal natural-deduction rules (`langlib
 *  rules`, LangLib/Studio/RulesView.lean; stories through studio/rules_story.py).
 *  Each rule is a card: a header (id, scheme, strict or defeasible, grounded
 *  label), its premises one per row above a line (solid strict, dashed
 *  defeasible, dotted unread), its conclusion below. The rules a premise rests
 *  on are listed under the card, indented, folded to one line until opened. Attacks are a margin
 *  list on each rule whose links scroll to and flash the other end. Hovering a
 *  quote highlights it in the source text. One component for the Studio and
 *  the deslop UI (src/rules-embed.tsx). docs/ui-rules.md has the evidence. */

export interface RPremise {
  t: string; tag: string; tagLabel?: string | null; quote: string; gloss?: string; para: string; sub: string | null; fail?: string
}
export interface RCq { i: number; q: string; attack: string; status: 'answered' | 'open' | 'pressed'; note: string }
export type Lab = 'in' | 'out' | 'undec'
export interface RRule {
  id: string; concl: string; quote: string; gloss?: string; para: string
  kind: 'strict' | 'defeasible' | 'unclassified'; scheme: string; side: 'text' | 'opponent'
  premises: RPremise[]; cqs: RCq[]; label: Lab; sceptic: Lab; thin: string[]; bare: boolean
  who?: string; group?: string; note?: string
}
export interface RAttack { src: string; tgt: string; how: 'rebut' | 'undercut' | 'undermine'; on: string | null; quote: string; ok: boolean; reaches: string[] }
export interface RulesData {
  root: string; rules: RRule[]; attacks: RAttack[]; bare: string[]; bareLeaves: string[]
  thin: { id: string; why: string[] }[]; ok: boolean; errors: string[]; groups?: { id: string; title: string }[]
}
export interface RulesDoc {
  id: string; title: string; kind?: string; note?: string; error?: string
  paragraphs: { name: string; text: string; heading?: string }[]; rules: RulesData
}

export const TAG: Record<string, string> = {
  fact: 'fact', example: 'example', citation: 'citation', authors: "authors' word", hedge: 'hedge', promise: 'promise',
  seen: 'seen', told: 'told', belief: 'belief', check: 'check',
}
/** Support that rests on the text's say-so rather than on something shown. */
const WEAK = new Set(['authors', 'hedge', 'promise'])
const HOWS: Record<string, [string, string]> = { rebut: ['rebuts', 'rebutted by'], undercut: ['undercuts', 'undercut by'], undermine: ['undermines', 'undermined by'] }
const LAB: Record<Lab, string> = { in: 'IN', out: 'OUT', undec: 'UNDEC' }
const KIND: Record<string, string> = { strict: 'strict', defeasible: 'defeasible', unclassified: 'unread' }

// ------------------------------------------------------------------ data

const docCache = new Map<string, RulesDoc>()

/** Fetch a rules document (cached by URL, so the panel and the inspector share it). */
export function useRulesDoc(url: string | null, version = 0): RulesDoc | null {
  const [doc, setDoc] = useState<RulesDoc | null>(() => url ? docCache.get(url) ?? null : null)
  useEffect(() => {
    if (!url) { setDoc(null); return }
    setDoc(docCache.get(url) ?? null)
    let live = true
    fetch(url).then(r => r.json()).then((d: RulesDoc) => { docCache.set(url, d); if (live) setDoc(d) })
      .catch(e => { if (live) setDoc({ id: '', title: '', error: String(e), paragraphs: [], rules: null as unknown as RulesData }) })
    return () => { live = false }
  }, [url, version])
  return doc
}

function index(d: RulesData) {
  const by = new Map(d.rules.map(r => [r.id, r]))
  const inn = new Map<string, RAttack[]>(), out = new Map<string, RAttack[]>(), parents = new Map<string, string[]>()
  for (const a of d.attacks) {
    if (!inn.has(a.tgt)) inn.set(a.tgt, [])
    inn.get(a.tgt)!.push(a)
    if (!out.has(a.src)) out.set(a.src, [])
    out.get(a.src)!.push(a)
  }
  for (const r of d.rules) for (const p of r.premises) if (p.sub && by.has(p.sub) && p.sub !== r.id) {
    if (!parents.has(p.sub)) parents.set(p.sub, [])
    if (!parents.get(p.sub)!.includes(r.id)) parents.get(p.sub)!.push(r.id)
  }
  const root = d.rules.find(r => r.concl === d.root && r.side === 'text') ?? null
  const under = (id: string, acc = new Set<string>()) => {
    if (acc.has(id)) return acc
    acc.add(id)
    for (const p of by.get(id)?.premises ?? []) if (p.sub && by.has(p.sub)) under(p.sub, acc)
    return acc
  }
  const inRoot = root ? under(root.id) : new Set<string>()
  const tops = d.rules.filter(r => !inRoot.has(r.id) && !(parents.get(r.id) ?? []).length)
  // rules on a cycle have parents but no top: list them too
  const shown = new Set(inRoot)
  for (const t of tops) under(t.id, shown)
  const orphans = d.rules.filter(r => !shown.has(r.id))
  return { by, inn, out, parents, root, tops: [...tops, ...orphans] }
}
type Index = ReturnType<typeof index>

// ------------------------------------------------------------------ highlighting the source

const norm = (s: string) => s.replace(/[’‘]/g, "'").replace(/[“”]/g, '"').replace(/[–—]/g, '-').toLowerCase()

function rangeOf(el: Element, quote: string): Range | null {
  const walker = document.createTreeWalker(el, NodeFilter.SHOW_TEXT, {
    acceptNode: n => (n.parentElement?.closest('.gutter, [data-nohl]') ? NodeFilter.FILTER_REJECT : NodeFilter.FILTER_ACCEPT),
  })
  let full = ''
  const map: [Text, number][] = []
  let space = true
  for (let n = walker.nextNode() as Text | null; n; n = walker.nextNode() as Text | null) {
    for (let i = 0; i < n.data.length; i++) {
      let c = n.data[i]
      if (/\s/.test(c)) { if (space) continue; c = ' '; space = true } else space = false
      full += norm(c)
      map.push([n, i])
    }
  }
  const q = norm(quote.replace(/\s+/g, ' ').trim().replace(/^["“]|["”]$/g, ''))
  if (!q) return null
  let at = full.indexOf(q), len = q.length
  if (at < 0) {   // an edited quote: anchor on its longest stretch that is verbatim
    for (const part of q.split(/\s*(?:\.\.\.|…|\[[^\]]*\])\s*/).sort((a, b) => b.length - a.length)) {
      if (part.length >= 8 && (at = full.indexOf(part)) >= 0) { len = part.length; break }
    }
  }
  if (at < 0) return null
  const r = document.createRange()
  r.setStart(map[at][0], map[at][1])
  r.setEnd(map[at + len - 1][0], map[at + len - 1][1] + 1)
  return r
}

function scroller(el: Element | null): HTMLElement | null {
  for (let e = el?.parentElement ?? null; e; e = e.parentElement) {
    const o = getComputedStyle(e).overflowY
    if ((o === 'auto' || o === 'scroll') && e.scrollHeight > e.clientHeight) return e
  }
  return null
}

let lit: Element | null = null
/** Highlight `quote` in paragraph `para` under `root` (the CSS Custom Highlight API;
 *  without it, the whole paragraph), scrolling it into view if it is out of sight. */
export function highlightQuote(root: ParentNode | null, para: string, quote: string) {
  clearHighlight()
  if (!root || !para) return
  const el = root.querySelector(`[data-para-name="${CSS.escape(para)}"]`)
  if (!el) return
  el.classList.add('rv-hl-para')
  lit = el
  const range = quote ? rangeOf(el, quote) : null
  const H = (window as unknown as { Highlight?: new (...r: Range[]) => unknown }).Highlight
  const reg = (CSS as unknown as { highlights?: Map<string, unknown> }).highlights
  if (range && H && reg) reg.set('rv-quote', new H(range))
  const box = (range ?? el).getBoundingClientRect()
  const sc = scroller(el)
  if (sc) {
    const s = sc.getBoundingClientRect()
    if (box.top < s.top + 8 || box.bottom > s.bottom - 8)
      sc.scrollTo({ top: sc.scrollTop + box.top - s.top - sc.clientHeight * 0.3, behavior: matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth' })
  }
}
export function clearHighlight() {
  lit?.classList.remove('rv-hl-para')
  lit = null;
  (CSS as unknown as { highlights?: Map<string, unknown> }).highlights?.delete('rv-quote')
}

// ------------------------------------------------------------------ the tree

interface Ctx {
  ix: Index; mode: 'label' | 'sceptic'; selected: string | null
  isOpen: (id: string, depth: number) => boolean; toggle: (id: string, depth: number) => void
  select: (id: string) => void; jump: (id: string) => void
  hover: (para: string, quote: string) => void; unhover: () => void
}
const C = createContext<Ctx>(null as unknown as Ctx)
const OPEN_DEPTH = 0

export function LabelBadge({ l, title }: { l: Lab; title?: string }) {
  return <span className={`rv-lab lab-${l}`} title={title}>{LAB[l]}</span>
}

function Quote({ text, gloss, para }: { text: string; gloss?: string; para: string }) {
  const { hover, unhover } = useContext(C)
  if (!text) return <span className="rv-gloss">{gloss}</span>
  return <span className="rv-q" onMouseEnter={() => hover(para, text)} onMouseLeave={unhover}
    title={para ? `¶ ${para}: hover to find it in the text` : undefined}>“{text}”</span>
}

function Tag({ p }: { p: RPremise }) {
  return <span className={`rv-tag ${WEAK.has(p.tag) ? 'weak' : ''}`} title={p.tagLabel ? `${TAG[p.tag] ?? p.tag}: ${p.tagLabel}` : undefined}>
    {p.tagLabel && p.tag !== 'check' ? p.tagLabel : TAG[p.tag] ?? p.tag}{p.tag === 'check' && p.tagLabel ? ` · ${p.tagLabel}` : ''}</span>
}

/** One premise per row: what it rests on at the left (a tag, or the rule that concludes it), the quote after. */
function Premise({ p, sub }: { p: RPremise; sub: string | null }) {
  const { toggle, isOpen, ix } = useContext(C)
  const sr = sub ? ix.by.get(sub) : null
  return <li className={`rv-prem ${p.fail ? 'fails' : ''}`}>
    <span className="rv-pk">{sub
      ? <button className={`rv-subref lab-${sr?.label ?? 'undec'}`} onClick={e => { e.stopPropagation(); toggle(sub, 1) }}
        title={isOpen(sub, 1) ? `fold ${sub}` : `show the rule ${sub} that concludes this, below`}>{isOpen(sub, 1) ? '▾' : '▸'} {sub}</button>
      : <Tag p={p} />}</span>
    <span className="rv-pq"><Quote text={p.quote} gloss={p.gloss || p.t} para={p.para} />
      {p.fail && <span className="rv-fail"> ✕ {p.fail}</span>}</span>
  </li>
}

function Margin({ r }: { r: RRule }) {
  const { ix, mode, jump } = useContext(C)
  const inn = ix.inn.get(r.id) ?? [], out = ix.out.get(r.id) ?? []
  const via = [...ix.inn.entries()].flatMap(([t, as]) => t === r.id ? [] : as.filter(a => a.ok && a.reaches.includes(r.id)))
  const pressed = mode === 'sceptic' ? r.cqs.filter(q => q.status === 'pressed') : []
  const lab = mode === 'label' ? r.label : r.sceptic
  const name = (id: string) => ix.by.get(id)?.side === 'opponent' ? `${id} (argued against)` : id
  const link = (id: string) => <button className="rv-link" onClick={e => { e.stopPropagation(); jump(id) }}>{name(id)}</button>
  const reinstated = lab === 'in' && inn.length > 0 && inn.every(a => (mode === 'label' ? ix.by.get(a.src)?.label : ix.by.get(a.src)?.sceptic) === 'out')
  if (!inn.length && !out.length && !via.length && !pressed.length) return null
  return <ul className="rv-margin">
    {inn.map((a, k) => <li key={`i${k}`} className={`in ${a.ok ? '' : 'fails'}`}>⟵ {HOWS[a.how]?.[1] ?? a.how} {link(a.src)}{a.on ? <> on “{a.on}”</> : null}
      {a.quote && <> <Quote text={a.quote} para={ix.by.get(a.src)?.para ?? ''} /></>}{!a.ok && <span className="dim"> (does not reach: a strict rule's conclusion stands)</span>}</li>)}
    {via.map((a, k) => <li key={`v${k}`} className="in via">⟵ through {link(a.tgt)}: {HOWS[a.how]?.[1] ?? a.how} {link(a.src)}</li>)}
    {pressed.map(q => <li key={`q${q.i}`} className="in pressed">⚑ CQ{q.i + 1} pressed ({q.attack}): {q.q}</li>)}
    {out.map((a, k) => <li key={`o${k}`} className={`out ${a.ok ? '' : 'fails'}`}>{HOWS[a.how]?.[0] ?? a.how} {link(a.tgt)} ⟶</li>)}
    {reinstated && <li className="dim">reinstated: every attacker is OUT</li>}
  </ul>
}

/** A rule as a card: a header (id, scheme, kind, label), its premises one per
 *  row above the line, the conclusion below. */
function RuleCard({ r, depth }: { r: RRule; depth: number }) {
  const cx = useContext(C)
  const lab = cx.mode === 'label' ? r.label : r.sceptic
  const other = cx.mode === 'label' ? r.sceptic : r.label
  return <div className={`rv-rule kind-${r.kind} side-${r.side} lab-${lab} ${cx.selected === r.id ? 'sel' : ''}`}
    data-rule={r.id} data-target={`irule:${r.id}`} onClick={e => { e.stopPropagation(); cx.select(r.id) }}>
    <div className="rv-rhead">
      {depth > 0 && <button className="rv-fold" onClick={e => { e.stopPropagation(); cx.toggle(r.id, depth) }} title="fold">▾</button>}
      <b className="rv-rid">{r.id}</b>
      {r.side === 'opponent' && <span className="rv-opp">argued against</span>}
      {r.who && <span className="rv-who">{r.who}</span>}
      <span className="rv-grow" />
      {r.para && <span className="rv-id">¶{r.para}</span>}
      <LabelBadge l={lab} title={other !== lab ? `${LAB[other]} ${cx.mode === 'label' ? "with the sceptic's questions" : "under the text's own attacks"}` : undefined} />
      {other !== lab && <span className="rv-was">{LAB[other]} {cx.mode === 'label' ? 'under the sceptic' : 'by the text'}</span>}
    </div>
    {r.premises.length > 0 && <ul className="rv-prems">
      {r.premises.map((p, k) => <Premise key={k} p={p} sub={p.sub && cx.ix.by.has(p.sub) && p.sub !== r.id ? p.sub : null} />)}
    </ul>}
    <div className="rv-bar"><span className={`rv-line ${r.kind}`} /><span className="rv-scheme">{r.scheme} · {KIND[r.kind] ?? r.kind}</span></div>
    <div className="rv-concl"><Quote text={r.quote} gloss={r.gloss || r.concl} para={r.para} /></div>
    <Margin r={r} />
  </div>
}

/** A rule and, indented under it, the rules its premises rest on: open ones
 *  as cards, folded ones as one-line rows. */
function RuleNode({ id, depth, path }: { id: string; depth: number; path: string[] }) {
  const cx = useContext(C)
  const r = cx.ix.by.get(id)
  if (!r) return <div className="rv-row dim">{id} (missing)</div>
  if (!cx.isOpen(id, depth)) {
    const lab = cx.mode === 'label' ? r.label : r.sceptic
    return <div className={`rv-row lab-${lab} side-${r.side} ${cx.selected === id ? 'sel' : ''}`} data-rule={id}
      onClick={e => { e.stopPropagation(); cx.toggle(id, depth) }} title="unfold this rule">
      <span className="rv-caret">▸</span><b className="rv-rid">{id}</b>
      <span className="rv-rowq">{r.quote ? `“${r.quote}”` : r.gloss || r.concl}</span>
      <span className="rv-rowmeta"><i className={`rv-sw ${r.kind}`} /><LabelBadge l={lab} /></span>
    </div>
  }
  const subs = [...new Set(r.premises.map(p => p.sub).filter((s): s is string => !!s && cx.ix.by.has(s) && s !== id && !path.includes(s)))]
  return <div className="rv-node">
    <RuleCard r={r} depth={depth} />
    {subs.length > 0 && <div className="rv-kids">
      {subs.map(s => <RuleNode key={s} id={s} depth={depth + 1} path={[...path, id]} />)}
    </div>}
  </div>
}

// ------------------------------------------------------------------ detail

/** A rule's critical questions, thin-support reasons and attacks (the detail panel and the Studio inspector). */
export function RuleDetail({ doc, id, onJump, onClose, root }: {
  doc: RulesDoc; id: string; onJump?: (id: string) => void; onClose?: () => void; root?: () => ParentNode | null
}) {
  const ix = useMemo(() => index(doc.rules), [doc])
  const r = ix.by.get(id)
  if (!r) return <div className="rv-detail dim">That rule is gone (the reading changed).</div>
  const inn = ix.inn.get(id) ?? [], out = ix.out.get(id) ?? []
  const link = (x: string) => onJump ? <button className="rv-link" onClick={() => onJump(x)}>{x}</button> : <b>{x}</b>
  const q = (text: string, para: string, gloss?: string) => text
    ? <span className="rv-q" onMouseEnter={() => highlightQuote(root?.() ?? document, para, text)} onMouseLeave={clearHighlight}>“{text}”</span>
    : <span className="rv-gloss">{gloss}</span>
  return <div className="rv-detail" data-target={`irule:${id}`}>
    <div className="rv-dhead">
      <b>{r.id}</b> <span className="dim">{r.scheme} · {KIND[r.kind] ?? r.kind}{r.side === 'opponent' ? ' · a position the text argues against' : ''}{r.para ? ` · ¶${r.para}` : ''}</span>
      {onClose && <button className="rv-x" onClick={onClose} title="close">×</button>}
    </div>
    <div className="rv-drow">{q(r.quote, r.para, r.gloss || r.concl)}</div>
    <div className="rv-drow"><LabelBadge l={r.label} /> under the text's own attacks · <LabelBadge l={r.sceptic} /> with the sceptic's pressed questions</div>
    {r.note && <div className="rv-drow dim">{r.note}</div>}
    <h4>Premises</h4>
    <ul className="rv-dlist">{r.premises.map((p, k) => <li key={k} className={p.fail ? 'fails' : ''}>
      {q(p.quote, p.para, p.gloss || p.t)} <span className={`rv-tag ${WEAK.has(p.tag) ? 'weak' : ''}`}>{p.tagLabel ?? TAG[p.tag] ?? p.tag}</span>
      {p.sub && ix.by.has(p.sub) && <> · from {link(p.sub)}</>}{p.fail && <div className="rv-fail">✕ {p.fail}</div>}</li>)}
      {!r.premises.length && <li className="dim">none: {r.kind === 'strict' ? 'it is asserted' : 'no grounds are recorded'}</li>}</ul>
    {r.cqs.length > 0 && <><h4>Critical questions</h4>
      <ul className="rv-dlist rv-cqs">{r.cqs.map(c => <li key={c.i} className={`cq-${c.status}`}>
        <span className={`rv-cq ${c.status}`}>{c.status === 'answered' ? '✓ answered' : c.status === 'pressed' ? '⚑ pressed' : '○ open'}</span>
        {' '}CQ{c.i + 1}. {c.q} <span className="dim">({c.attack})</span>{c.note && <div className="rv-note">{c.note}</div>}</li>)}</ul></>}
    {(r.thin.length > 0 || r.bare) && <><h4>Thin support</h4><ul className="rv-dlist">
      {r.thin.map((t, k) => <li key={k} className="warn">{t}</li>)}
      {r.bare && <li className="warn">every leaf under it is the authors' word, a hedge or a promise</li>}</ul></>}
    {(inn.length > 0 || out.length > 0) && <><h4>Attacks</h4><ul className="rv-dlist">
      {inn.map((a, k) => <li key={`i${k}`}>{HOWS[a.how]?.[1] ?? a.how} {link(a.src)}{a.on ? ` on “${a.on}”` : ''}{a.quote ? <>: {q(a.quote, ix.by.get(a.src)?.para ?? '')}</> : null}
        {!a.ok && <span className="dim"> (fails: restricted rebut)</span>}{a.reaches.length > 1 && <div className="dim">reaches {a.reaches.filter(x => x !== a.tgt).join(', ')}</div>}</li>)}
      {out.map((a, k) => <li key={`o${k}`}>{HOWS[a.how]?.[0] ?? a.how} {link(a.tgt)}{a.quote ? <>: {q(a.quote, r.para)}</> : null}</li>)}</ul></>}
    {(ix.parents.get(id) ?? []).length > 0 && <div className="rv-drow dim">a premise of {(ix.parents.get(id) ?? []).map((x, k) => <React.Fragment key={x}>{k ? ', ' : ''}{link(x)}</React.Fragment>)}</div>}
  </div>
}

// ------------------------------------------------------------------ the view

function Section({ title, ids, note }: { title: string; ids: string[]; note?: string }) {
  const [shut, setShut] = useState(false)
  if (!ids.length) return null
  return <section className="rv-sec">
    <h4 onClick={() => setShut(!shut)} className="rv-sech">{shut ? '▸' : '▾'} {title} · {ids.length}</h4>
    {!shut && <>{note && <div className="rv-secnote">{note}</div>}{ids.map(id => <div className="rv-top" key={id}><RuleNode id={id} depth={0} path={[]} /></div>)}</>}
  </section>
}

export function RulesView({ doc, textRoot, mdUrl, detail = 'below', selected: selProp, onSelect }: {
  doc: RulesDoc
  /** where the source text is (paragraphs carry data-para-name) */
  textRoot?: () => ParentNode | null
  mdUrl?: string
  /** 'below': the detail panel under the tree; 'none': the host shows it (onSelect) */
  detail?: 'below' | 'none'
  selected?: string | null
  onSelect?: (id: string | null) => void
}) {
  const ix = useMemo(() => doc.rules ? index(doc.rules) : null, [doc])
  const [mode, setMode] = useState<'label' | 'sceptic'>(() => { try { return (localStorage.getItem('rules.mode') as 'label' | 'sceptic') || 'label' } catch { return 'label' } })
  const [open, setOpen] = useState<Map<string, boolean>>(new Map())
  const [selLocal, setSelLocal] = useState<string | null>(null)
  const selected = selProp !== undefined ? selProp : selLocal
  const treeRef = useRef<HTMLDivElement>(null)
  const setM = (m: 'label' | 'sceptic') => { setMode(m); try { localStorage.setItem('rules.mode', m) } catch { /* private mode */ } }
  const select = useCallback((id: string | null) => { setSelLocal(id); onSelect?.(id) }, [onSelect])
  const isOpen = useCallback((id: string, depth: number) => open.get(id) ?? depth <= OPEN_DEPTH, [open])
  const toggle = useCallback((id: string, depth: number) => setOpen(m => new Map(m).set(id, !(m.get(id) ?? depth <= OPEN_DEPTH))), [])
  const jump = useCallback((id: string) => {
    if (!ix) return
    // open one chain of rules from a top down to `id`, then scroll to it and flash it
    setOpen(m => {
      const n = new Map(m)
      n.set(id, true)
      for (let x = id, guard = 0; guard < 50; guard++) {
        const ps = ix.parents.get(x) ?? []
        if (!ps.length) break
        x = ps[0]
        n.set(x, true)
      }
      return n
    })
    select(id)
    setTimeout(() => {
      const el = treeRef.current?.querySelector<HTMLElement>(`[data-rule="${CSS.escape(id)}"]`)
      if (!el) return
      el.scrollIntoView({ block: 'center', behavior: matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth' })
      el.classList.remove('rv-flash'); void el.offsetWidth; el.classList.add('rv-flash')
    }, 30)
  }, [ix, select])
  const hover = useCallback((para: string, quote: string) => highlightQuote(textRoot?.() ?? document, para, quote), [textRoot])
  useEffect(() => clearHighlight, [])
  const download = async () => {
    if (!mdUrl) return
    const t = await (await fetch(mdUrl)).text()
    const a = document.createElement('a')
    a.href = URL.createObjectURL(new Blob([t], { type: 'text/markdown' }))
    a.download = `${(doc.title || 'rules').replace(/[^\w-]+/g, '-').slice(0, 60)}.rules.md`
    a.click()
    setTimeout(() => URL.revokeObjectURL(a.href), 2000)
  }

  if (doc.error) return <div className="rv-root"><div className="rv-err">The rules could not be read: {doc.error}</div></div>
  if (!ix) return <div className="rv-root dim">no rules</div>
  const d = doc.rules
  const lab = (r: RRule) => mode === 'label' ? r.label : r.sceptic
  const count = (l: Lab) => d.rules.filter(r => lab(r) === l).length
  const tops = ix.tops.filter(r => r.id !== ix.root?.id)
  const groups = d.groups?.length ? d.groups : null
  const cx: Ctx = { ix, mode, selected, isOpen, toggle, select, jump, hover, unhover: clearHighlight }
  return <C.Provider value={cx}>
    <div className="rv-root">
      <div className="rv-head">
        <div className="rv-stats">{d.rules.length} rules · {d.rules.filter(r => r.kind === 'strict').length} strict · {d.attacks.length} attacks ·
          {' '}<LabelBadge l="in" /> {count('in')} <LabelBadge l="out" /> {count('out')} <LabelBadge l="undec" /> {count('undec')}
          {!d.ok && <span className="rv-bad"> · the reading has errors</span>}</div>
        <div className="rv-ctl">
          <span className="rv-seg" role="group" aria-label="labelling">
            <button className={mode === 'label' ? 'on' : ''} onClick={() => setM('label')} title="grounded labelling under the attacks the text itself makes">text's own attacks</button>
            <button className={mode === 'sceptic' ? 'on' : ''} onClick={() => setM('sceptic')} title="every critical question the sceptic presses is an attacker too">with the sceptic's questions</button>
          </span>
          <button className="rv-btn" onClick={() => setOpen(new Map(d.rules.map(r => [r.id, true])))}>unfold all</button>
          <button className="rv-btn" onClick={() => setOpen(new Map(d.rules.map(r => [r.id, false])))}>fold all</button>
          {mdUrl && <button className="rv-btn" onClick={download} title="the rules as markdown (tools/house/rules_md.py)">Markdown</button>}
        </div>
        <div className="rv-legend">
          <span><i className="rv-sw strict" />strict</span><span><i className="rv-sw defeasible" />defeasible</span>
          {d.rules.some(r => r.kind === 'unclassified') && <span><i className="rv-sw unclassified" />scheme not read yet</span>}
          <span className="rv-tag">fact</span><span className="rv-tag weak">authors' word</span>
          <span>hover a quote to find it in the text · click a rule for its questions{detail === 'none' ? '' : ''}</span>
        </div>
        {doc.note && <div className="rv-secnote">{doc.note}</div>}
        {d.errors.length > 0 && <ul className="rv-err">{d.errors.map((e, k) => <li key={k}>{e}</li>)}</ul>}
      </div>
      <div className="rv-tree" ref={treeRef} onClick={() => select(null)}>
        {ix.root && <Section title="The main argument, down to its conclusion" ids={[ix.root.id]} />}
        {groups ? <>
          {groups.map(g => <Section key={g.id} title={g.title} ids={tops.filter(r => r.group === g.id).map(r => r.id)} />)}
          <Section title="Other rules" ids={tops.filter(r => !groups.some(g => g.id === r.group)).map(r => r.id)} />
        </> : <>
          <Section title={ix.root ? 'Other arguments of the text' : 'The text\'s arguments'} ids={tops.filter(r => r.side === 'text').map(r => r.id)}
            note={ix.root ? 'Rules the main argument does not rest on.' : undefined} />
          <Section title="Positions the text argues against" ids={tops.filter(r => r.side === 'opponent').map(r => r.id)} />
        </>}
      </div>
      {detail === 'below' && selected && ix.by.has(selected) && <div className="rv-dock">
        <RuleDetail doc={doc} id={selected} onJump={jump} onClose={() => select(null)} root={textRoot} /></div>}
    </div>
  </C.Provider>
}

/** The source text, paragraph by paragraph with its headings, for hosts that do not show it already. */
export function RulesText({ doc, side }: { doc: RulesDoc; side?: React.ReactNode }) {
  return <article className="rv-text">
    <h2 className="rv-title">{doc.title}</h2>
    {side}
    {doc.paragraphs.map(p => <React.Fragment key={p.name}>
      {p.heading && <h3 className="rv-heading">{p.heading}</h3>}
      <p className="rv-para" data-para-name={p.name}><span className="rv-pn" data-nohl>{p.name}</span>{p.text}</p>
    </React.Fragment>)}
    {!doc.paragraphs.length && <p className="dim">No text.</p>}
  </article>
}
