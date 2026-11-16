import React, { useState } from 'react'
import type { StyleReport } from './types'

/** Style verdicts (`langlib style`, `house`, `academic`): each named style's
 *  rules, failing first, with the measured ratio the rule reads. Every
 *  question here is a lookup, so a list (docs/ui-visualisation.md §8). */

function ratio(rule: string, f?: Record<string, number | boolean>): string {
  if (!f) return ''
  // "agentless / clauses ≤ 1/10": show the measured numerator and denominator
  const m = rule.match(/^(\w+)(?: \/ (\w+))? [≤≥]/)
  if (!m) return ''
  const a = f[m[1]], b = m[2] ? f[m[2]] : undefined
  if (typeof a !== 'number') return ''
  return b === undefined ? `measured ${a}` : typeof b === 'number' ? `measured ${a}/${b}` : ''
}

export function StyleView({ reports }: { reports: [string, StyleReport | null | undefined][] }) {
  const [all, setAll] = useState(false)
  const shown = reports.filter(([, r]) => r)
  if (!shown.length) return <div className="storyview dim">No style report for this story.</div>
  return <div className="storyview styleview">
    <label className="row"><input type="checkbox" checked={all} onChange={e => setAll(e.target.checked)} /> show the rules that hold too</label>
    {shown.map(([src, r]) => r!.error ? <section key={src}><h3>{src}</h3><pre className="err">{r!.error}</pre></section> :
      <section key={src}>
        <h3>{src}{r!.pov && <span className="dim"> · point of view {r!.pov}</span>}</h3>
        {r!.styles.map(s => {
          const failing = s.rules.filter(x => !x.holds)
          const holds = s.holds ?? failing.length === 0
          return <div key={s.name} className="stylebox" data-target={`style:${src}:${encodeURIComponent(s.name)}`}>
            <h4><span className={holds ? 'ok' : 'bad'}>{holds ? '✓ holds' : `✕ ${failing.length} of ${s.rules.length} rules fail`}</span> · {s.name}</h4>
            <ul className="rules">{[...failing, ...(all ? s.rules.filter(x => x.holds) : [])].map(x =>
              <li key={x.name} className={x.holds ? 'ok' : 'bad'} data-target={`rule:${src}:${encodeURIComponent(s.name)}:${encodeURIComponent(x.name)}`}>
                <span className="st">{x.holds ? '✓' : '✕'}</span> {x.name} <code>{x.rule}</code> <span className="dim">{ratio(x.rule, r!.features)}</span></li>)}</ul>
          </div>
        })}
        {r!.features && all && <details><summary className="dim">measured features</summary>
          <div className="chips">{Object.entries(r!.features).map(([k, v]) => <span key={k} className="chip">{k} {String(v)}</span>)}</div></details>}
      </section>)}
  </div>
}
