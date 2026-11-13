import React, { useEffect, useState } from 'react'
import type { Report } from './types'
import { charColour, charName } from './Logic'

function Spark({ values, colour }: { values: number[]; colour: string }) {
  const max = Math.max(3, ...values)
  const w = 120, h = 22
  const pts = values.map((v, i) => `${(i / Math.max(1, values.length - 1)) * (w - 4) + 2},${h - 3 - (v / max) * (h - 6)}`).join(' ')
  return <svg width={w} height={h} className="spark"><polyline points={pts} fill="none" stroke={colour} strokeWidth={1.6} />
    {values.map((v, i) => <circle key={i} cx={(i / Math.max(1, values.length - 1)) * (w - 4) + 2} cy={h - 3 - (v / max) * (h - 6)} r={1.4} fill={colour}><title>{`after ¶${i}: ${v}`}</title></circle>)}</svg>
}

export function StoryView({ report, current }: { report: Report; current: number }) {
  const at = report.paragraphs[Math.max(0, current)]?.state ?? report.start
  const facts = report.atoms
  const views = at.views
  const pairs = Object.keys(report.start.bonds)
  const dims = ['trust', 'attraction', 'affection', 'tension']
  const series = (pair: string, dim: string) =>
    [report.start, ...report.paragraphs.map(p => p.state)].map(s => s.bonds[pair]?.[dim] ?? 0)
  const v = report.verdict
  return (
    <div className="storyview">
      <section>
        <h3>Verdict</h3>
        <div className={`big ${v.valid ? 'ok' : v.plausible ? 'warn' : 'bad'}`}>
          {v.valid ? 'valid' : v.plausible ? `plausible under ${v.assumptions} assumption${v.assumptions === 1 ? '' : 's'}` : 'failing'}
        </div>
        {v.failure && <div className="row bad">first failure at event {v.failure.i}: {v.failure.why}</div>}
        <div className="row dim">timeline {report.time.consistent ? 'consistent' : 'inconsistent'} ({report.time.constraints} constraints); told {report.time.toldOrder ? 'in story order' : 'out of order'}</div>
      </section>

      <section>
        <h3>Cast</h3>
        {report.characters.map(c => <div key={c.id} className="row">
          <b style={{ color: charColour(report, c.id) }}>{c.name}</b> <span className="dim">({c.pron})</span> · {c.traits.join(', ') || 'no traits'} · values {c.values.join(' > ')}
        </div>)}
      </section>

      <section>
        <h3>Who believes what, after ¶ {report.paragraphs[current]?.name ?? 'start'}</h3>
        <table className="matrix">
          <thead><tr><th />{report.characters.map(c => <th key={c.id} style={{ color: charColour(report, c.id) }}>{c.name}</th>)}<th className="dim">true?</th></tr></thead>
          <tbody>{facts.map(f => (
            <tr key={f.id}><td className="fl">{f.label}</td>
              {report.characters.map(c => {
                const vs = views[c.id] ?? []
                const yes = vs.some(l => l.lit === f.id), no = vs.some(l => l.lit === `!${f.id}`)
                const wrong = (yes && !f.truth) || (no && f.truth)
                return <td key={c.id} className={`cell ${wrong ? 'wrong' : ''}`} title={wrong ? 'false belief' : ''}>{yes ? '✓' : no ? '✗' : '·'}</td>
              })}
              <td className="dim">{f.truth ? '✓' : '✗'}</td></tr>))}</tbody>
        </table>
      </section>

      <section>
        <h3>Bonds across the story</h3>
        <table className="bonds"><tbody>{pairs.flatMap(pair => dims.filter(d => series(pair, d).some(x => x > 0)).map(d => {
          const [a, b] = pair.split('>')
          return <tr key={pair + d}><td><span style={{ color: charColour(report, a) }}>{charName(report, a)}</span>→<span style={{ color: charColour(report, b) }}>{charName(report, b)}</span></td>
            <td className="dim">{d}</td><td><Spark values={series(pair, d)} colour={charColour(report, a)} /></td></tr>
        }))}</tbody></table>
        {at.consent.length > 0 && <><h4>Consent in force</h4>{at.consent.map((c, i) => <div key={i} className="row consent">✓ {c}</div>)}</>}
      </section>

      {report.beats && <section>
        <h3>Beats {report.beats.valid ? <span className="badge valid">valid</span> : <span className="badge failing">invalid</span>} {report.beats.refines ? <span className="badge valid">plans refine beats</span> : <span className="badge failing">plans do not refine beats</span>}</h3>
        {report.beats.failure && <div className="row bad">{report.beats.failure.why}</div>}
        <ol className="beats">{report.beats.story.map((b, i) => {
          const v = report.beats!.vocab.find(x => x.id === b)
          const got = report.beats!.abstracted[i]
          return <li key={i} className={got === b ? 'ok' : 'bad'}><b>{b}</b> {v?.label}
            {v && v.pre.length > 0 && <span className="dim"> · needs {v.pre.join(', ')}</span>}
            {got !== b && <span className="bad"> · plans give {got ?? 'nothing'}</span>}</li>
        })}</ol>
      </section>}
    </div>
  )
}

export function ProofView({ report, onProve }: { report: Report; onProve: () => void }) {
  const p = report.proofs
  const thms = Object.entries(p?.theorems ?? {})
  return (
    <div className="storyview">
      <section>
        <h3>Lean <button className="btn small" onClick={onProve}>re-check</button></h3>
        <div className={`big ${p.status === 'ok' ? 'ok' : p.status === 'running' ? 'warn' : p.status === 'none' ? '' : 'bad'}`}>
          {p.status === 'ok' ? `${thms.length} theorems checked by the kernel` : p.status === 'running' ? 'checking…' : p.status === 'none' ? 'not yet checked' : 'some proofs failed'}
          {p.secs !== undefined && <span className="dim"> · {p.secs}s</span>}
        </div>
        {p.file && <div className="row dim"><code>{p.file}</code></div>}
        {p.error && <pre className="err">{p.error}</pre>}
        {(p.guards ?? []).map((g, i) => <div key={i} className="row bad">{g}</div>)}
      </section>
      <section>
        <ul className="thms">{thms.map(([n, t]) => <li key={n} className={t.ok ? 'ok' : t.ok === false ? 'bad' : ''}>
          <span className="st">{t.ok ? '✓' : t.ok === false ? '✕' : '…'}</span> <code>{t.statement}</code>{t.error && <pre className="err">{t.error}</pre>}</li>)}</ul>
      </section>
    </div>
  )
}

interface Run { workflow: string; steps: Record<string, unknown>[] }

export function RunsView({ report }: { report: Report }) {
  const [runs, setRuns] = useState<Run[]>([])
  useEffect(() => { fetch(`/api/story/${report.name}/runs`).then(r => r.json()).then(setRuns).catch(() => {}) }, [report])
  const summary = report.summary as Record<string, Record<string, number>> | undefined
  return (
    <div className="storyview">
      {summary && <section><h3>Workflows compared</h3>
        <table className="matrix"><thead><tr><th />{Object.keys(summary).map(w => <th key={w}>{w}</th>)}</tr></thead>
          <tbody>{[...new Set(Object.values(summary).flatMap(o => Object.keys(o)))].map(k => <tr key={k}><td className="fl">{k}</td>
            {Object.keys(summary).map(w => <td key={w}>{String(summary[w][k] ?? '')}</td>)}</tr>)}</tbody></table></section>}
      {runs.map(r => <section key={r.workflow}><h3>{r.workflow}</h3>
        <ul className="runlog">{r.steps.map((s, i) => <li key={i}>
          <span className="dim">{String(s.para ?? '')} {String(s.stage ?? '')}</span> {String(s.note ?? '')}
          {s.ok === false && <span className="bad"> ✕</span>}{s.secs !== undefined && <span className="dim"> {String(s.secs)}s</span>}</li>)}</ul></section>)}
      {!runs.length && !summary && <section className="dim">No workflow runs recorded yet.</section>}
    </div>
  )
}
