import React, { useRef, useState } from 'react'
import { RuleDetail, RulesText, RulesView, useRulesDoc } from './Rules'
import { ContextMenu, targetsAt, type Menu, type MenuItem } from './Inspector'

/** The Studio's hosts for the Rules view (Rules.tsx): the Rules tab beside a
 *  paper's or a story's Argument tab (the text is the prose pane already on
 *  the left), its Inspect entry, and a whole page for documents that are only
 *  an argument reading (deslop sides, the Death Note arc). */

const url = (doc: string) => `/api/rules?doc=${encodeURIComponent(doc)}`
const mdUrl = (doc: string) => `/api/rules/md?doc=${encodeURIComponent(doc)}`

export function RulesPanel({ doc, textRoot, version = 0 }: { doc: string; textRoot: () => ParentNode | null; version?: number }) {
  const d = useRulesDoc(url(doc), version)
  if (!d) return <div className="storyview dim">Reading the rules…</div>
  return <div className="rv-host"><RulesView doc={d} textRoot={textRoot} mdUrl={mdUrl(doc)} /></div>
}

/** Right-click → Inspect on a rule. */
export function RuleInspect({ doc, id, textRoot, onPick }: { doc: string; id: string; textRoot: () => ParentNode | null; onPick: (id: string) => void }) {
  const d = useRulesDoc(url(doc))
  if (!d) return <div className="storyview dim">Reading the rules…</div>
  return <div className="inspector"><RuleDetail doc={d} id={id} onJump={onPick} root={textRoot} /></div>
}

/** A menu entry for each rule under a right-click. */
export function ruleItems(targets: string[], inspect: (id: string) => void): MenuItem[] {
  return targets.filter(t => t.startsWith('irule:')).map(t => ({ label: `Inspect rule ${t.slice(6)}`, run: () => inspect(t.slice(6)) }))
}

type RTab = 'rules' | 'inspect'

/** A document read only as an argument: its text on the left, its rules on the right. */
export function RulesMain({ doc, size, face }: { doc: string; size: string; face: string }) {
  const d = useRulesDoc(url(doc))
  const prose = useRef<HTMLDivElement>(null)
  const [tab, setTab] = useState<RTab>('rules')
  const [inspecting, setInspecting] = useState<string | null>(null)
  const [menu, setMenu] = useState<Menu | null>(null)
  const root = () => prose.current
  const onContextMenu = (e: React.MouseEvent) => {
    const items = ruleItems(targetsAt(e.target as HTMLElement), id => { setInspecting(id); setTab('inspect') })
    if (!items.length) return
    e.preventDefault()
    setMenu({ x: e.clientX, y: e.clientY, items })
  }
  if (!d) return <div className="main"><div className="prose-pane"><div className="prose"><p className="para empty">Reading the argument…</p></div></div></div>
  return (
    <div className="main" onContextMenu={onContextMenu}>
      <div className="prose-pane" ref={prose}>
        <div className={face === 'sans' ? 'rv-sans' : ''} style={{ ['--rv-size' as string]: `${Math.max(15, Number(size) - 3)}px` }}><RulesText doc={d} /></div>
      </div>
      <aside className="right rv-wide">
        <nav className="tabs">{(['rules', ...(inspecting ? ['inspect'] : [])] as RTab[]).map(t =>
          <button key={t} className={tab === t ? 'on' : ''} onClick={() => setTab(t)}>{t}</button>)}</nav>
        {tab === 'rules' && <RulesPanel doc={doc} textRoot={root} />}
        {tab === 'inspect' && inspecting && <div className="logic"><RuleInspect doc={doc} id={inspecting} textRoot={root} onPick={setInspecting} /></div>}
      </aside>
      {menu && <ContextMenu menu={menu} onClose={() => setMenu(null)} />}
    </div>
  )
}
