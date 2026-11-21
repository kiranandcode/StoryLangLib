import React, { useEffect, useRef, useState } from 'react'
import { createPortal } from 'react-dom'
import { createRoot, type Root } from 'react-dom/client'
import { RuleDetail, RulesText, RulesView, useRulesDoc } from './Rules'
import './rules-embed.css'

/** The Rules view for pages outside the Studio (the deslop UI): the same
 *  Rules.tsx, built on its own by `npm run build:rules` (vite.rules.config.ts)
 *  into tools/house/deslop_ui/rules-view/. The page calls
 *
 *    RulesEmbed.mount(el, { url, mdUrl, sides?, side?, onSide?, detailEl? })
 *
 *  `url` serves a rules document (studio/rules_docs.py), `detailEl` is where
 *  the detail panel goes (the page's inspector), and the page's theme reaches
 *  the view through rules-embed.css. */

export interface EmbedOpts {
  url: string; mdUrl?: string
  sides?: { id: string; label: string }[]; side?: string; onSide?: (id: string) => void
  detailEl?: HTMLElement | null
}

function RulesApp({ url, mdUrl, sides, side, onSide, detailEl }: EmbedOpts) {
  const doc = useRulesDoc(url)
  const text = useRef<HTMLDivElement>(null)
  const [sel, setSel] = useState<string | null>(null)
  const [menu, setMenu] = useState<{ x: number; y: number; id: string } | null>(null)
  useEffect(() => setSel(null), [url])
  useEffect(() => {
    if (!menu) return
    const close = () => setMenu(null)
    window.addEventListener('mousedown', close)
    window.addEventListener('keydown', close)
    return () => { window.removeEventListener('mousedown', close); window.removeEventListener('keydown', close) }
  }, [menu])
  const onContextMenu = (e: React.MouseEvent) => {
    const el = (e.target as HTMLElement).closest<HTMLElement>('[data-target^="irule:"]')
    if (!el) return
    e.preventDefault()
    setMenu({ x: e.clientX, y: e.clientY, id: el.dataset.target!.slice(6) })
  }
  if (!doc) return <div className="rv-embed"><p className="rv-wait">Reading the rules…</p></div>
  const root = () => text.current
  const detail = sel && doc.rules ? <div className="rv-embed rv-embed-detail">
    <RuleDetail doc={doc} id={sel} onJump={setSel} onClose={() => setSel(null)} root={root} /></div> : null
  return <div className="rv-embed rv-app" onContextMenu={onContextMenu}>
    <div className="rv-col rv-col-text" ref={text}>
      <RulesText doc={doc} side={sides && sides.length > 1 ? <div className="rv-sides">{sides.map(s =>
        <button key={s.id} className={s.id === side ? 'on' : ''} onClick={() => onSide?.(s.id)}>{s.label}</button>)}</div> : null} />
    </div>
    <div className="rv-col rv-col-rules">
      <RulesView doc={doc} textRoot={root} mdUrl={mdUrl} detail={detailEl ? 'none' : 'below'} selected={detailEl ? sel : undefined} onSelect={setSel} />
    </div>
    {detailEl && detail && createPortal(detail, detailEl)}
    {menu && <ul className="rv-menu" style={{ left: Math.min(menu.x, innerWidth - 200), top: Math.min(menu.y, innerHeight - 60) }} onMouseDown={e => e.stopPropagation()}>
      <li onClick={() => { setSel(menu.id); setMenu(null) }}>Inspect rule {menu.id}</li></ul>}
  </div>
}

const roots = new WeakMap<HTMLElement, Root>()

export function mount(el: HTMLElement, opts: EmbedOpts) {
  let r = roots.get(el)
  if (!r) { r = createRoot(el); roots.set(el, r) }
  r.render(<RulesApp {...opts} />)
}

export function unmount(el: HTMLElement) {
  roots.get(el)?.unmount()
  roots.delete(el)
}
