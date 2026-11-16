import React from 'react'
import type { ConsentReport, ExtReport, Readings, Report } from './types'
import { charColour, charName } from './Logic'
import { consentScenes, parseFeel, parseNeeds, parseTie, type CEvent, type Scene } from './readings'

/** What the logic holds beyond places and beliefs (docs/ui-visualisation.md §8):
 *  ties and affect as sparklines on a shared scale; care (needs, offers,
 *  tending, harm); identity knowledge as a who-knows-what table with harms in
 *  words; consent as lanes per scene, with limits, check-ins and withdrawals
 *  written out (never colour alone). */

const SPARK_H = 24

/** One sparkline per series, all on one y-scale (`max`), the current paragraph marked. */
function Spark({ values, max, colour, current, label }: { values: number[]; max: number; colour: string; current: number; label: string }) {
  const N = values.length
  const x = (k: number) => N <= 1 ? 50 : (k / (N - 1)) * 100
  const y = (v: number) => SPARK_H - 2 - (v / Math.max(1, max)) * (SPARK_H - 4)
  return <svg className="spark2" viewBox={`0 0 100 ${SPARK_H}`} preserveAspectRatio="none" height={SPARK_H} aria-label={label}>
    <line x1={0} x2={100} y1={y(0)} y2={y(0)} className="sbase" />
    <polyline points={values.map((v, k) => `${x(k)},${y(v)}`).join(' ')} fill="none" stroke={colour} strokeWidth={1.6} vectorEffect="non-scaling-stroke" />
    {current >= 0 && current < N && <line x1={x(current)} x2={x(current)} y1={0} y2={SPARK_H} className="scur" vectorEffect="non-scaling-stroke" />}
  </svg>
}

function SparkRows({ rows, current }: { rows: { key: string; label: React.ReactNode; values: number[]; colour: string; target?: string }[]; current: number }) {
  const max = Math.max(1, ...rows.flatMap(r => r.values))
  return <div className="sparkgrid">
    {rows.map(r => <React.Fragment key={r.key}>
      <div className="sl" data-target={r.target}>{r.label}</div>
      <Spark values={r.values} max={max} colour={r.colour} current={current} label={r.key} />
      <div className="sv">{r.values[current] ?? 0}<span className="dim">/{max}</span></div>
    </React.Fragment>)}
  </div>
}

function TiesAffect({ report, ext, current }: { report: Report; ext: ExtReport; current: number }) {
  const ties = new Map<string, { a: string; rel: string; b: string }>()
  const feels = new Map<string, { who: string; emo: string }>()
  for (const p of ext.paragraphs) {
    for (const s of p.ties) { const t = parseTie(s); if (t) ties.set(`${t.a} ${t.rel} ${t.b}`, t) }
    for (const s of p.feels) { const f = parseFeel(s); if (f) feels.set(`${f.who} ${f.emo}`, f) }
  }
  const tieVals = (k: string) => ext.paragraphs.map(p => p.ties.map(parseTie).find(t => t && `${t.a} ${t.rel} ${t.b}` === k)?.n ?? 0)
  const feelVals = (k: string) => ext.paragraphs.map(p => p.feels.map(parseFeel).find(f => f && `${f.who} ${f.emo}` === k)?.n ?? 0)
  // ties that never change are listed, not drawn
  const tieRows = [...ties].map(([k, t]) => ({ k, t, v: tieVals(k) }))
  const moving = tieRows.filter(r => new Set(r.v).size > 1), steady = tieRows.filter(r => new Set(r.v).size <= 1)
  const C = (id: string) => <span style={{ color: charColour(report, id) }}>{charName(report, id)}</span>
  return <>
    {feels.size > 0 && <section><h3>Feelings</h3>
      <SparkRows current={current} rows={[...feels].map(([k, f]) => ({ key: k, label: <>{C(f.who)} {f.emo}</>, values: feelVals(k), colour: charColour(report, f.who), target: `feel:${f.who}:${f.emo}` }))} />
    </section>}
    {tieRows.length > 0 && <section><h3>Ties</h3>
      {moving.length > 0 && <SparkRows current={current} rows={moving.map(r => ({ key: r.k, label: <>{C(r.t.a)} {r.t.rel} {C(r.t.b)}</>, values: r.v, colour: charColour(report, r.t.a), target: `tie:${r.t.a}:${r.t.rel}:${r.t.b}` }))} />}
      {steady.length > 0 && <div className="row dim">unchanged throughout: {steady.map((r, i) => <span key={r.k} data-target={`tie:${r.t.a}:${r.t.rel}:${r.t.b}`}>{i ? ', ' : ''}{charName(report, r.t.a)} {r.t.rel} {charName(report, r.t.b)} ({r.v[0]})</span>)}</div>}
    </section>}
  </>
}

const CARE = new Set(['harm', 'offer', 'accept', 'acceptQuietly', 'decline', 'tend', 'shield'])
const ID = new Set(['introduce', 'tellName', 'learnName', 'coin', 'call', 'assume', 'learnPron', 'tellPron', 'refer', 'disclose', 'out'])

function Care({ report, ext, current }: { report: Report; ext: ExtReport; current: number }) {
  const p = ext.paragraphs[current]
  const evs = ext.paragraphs.slice(0, current + 1).flatMap(q => q.events.filter(e => CARE.has(e.e.split(' ')[0])).map(e => ({ ...e, para: q.name })))
  if (!evs.length && !(p?.needs.length)) return null
  const VERB: Record<string, string> = { harm: 'harms', offer: 'offers', accept: 'accepts', acceptQuietly: 'quietly accepts', decline: 'declines', tend: 'tends to', shield: 'shields' }
  return <section><h3>Care, by ¶ {p?.name}</h3>
    {(p?.needs ?? []).map(s => { const n = parseNeeds(s); return n && <div key={s} className="row" data-target={`needs:${n.who}`}>
      <b style={{ color: charColour(report, n.who) }}>{charName(report, n.who)}</b> still needs: <span className="chips">{n.needs.map(k => <span key={k} className="chip">{k}</span>)}</span></div> })}
    <ul className="carelog">{evs.slice(-12).map((e, i) => { const [k, a, b, x] = e.e.split(' '); return <li key={i} className={e.ok ? (k === 'harm' ? 'warn' : '') : 'bad'} data-target={`ext:${e.para}:${e.at}`}>
      <span className="dim">¶{e.para}</span> {charName(report, a)} {VERB[k] ?? k} {charName(report, b)}{x ? <>{k === 'shield' ? ' from ' : ': '}{k === 'shield' ? charName(report, x) : x}</> : null}{!e.ok && ` (refused: ${e.why})`}</li> })}</ul>
    {evs.length > 12 && <div className="row dim">and {evs.length - 12} earlier</div>}
  </section>
}

function Identity({ report, ext, current }: { report: Report; ext: ExtReport; current: number }) {
  const p = ext.paragraphs[current]
  const knows = p?.knows ?? []
  const harms = p?.harms ?? []
  const idEvents = ext.paragraphs.slice(0, current + 1).flatMap(q => q.events.filter(e => ID.has(e.e.split(' ')[0]) && e.e.split(' ')[0] !== 'refer').map(e => ({ ...e, para: q.name })))
  if (!knows.length && !harms.length && !idEvents.length) return null
  const people = [...new Set(knows.map(k => k.of))]
  const knowers = [...new Set(knows.map(k => k.who))]
  return <section><h3>Who knows what of whom, by ¶ {p?.name}</h3>
    {knows.length > 0 ? <div className="idtable">
      {people.map(of => <div key={of} className="idperson" data-target={`char:${of}`}>
        <div className="idof">about <b style={{ color: charColour(report, of) }}>{charName(report, of)}</b></div>
        {knowers.filter(w => w !== of).map(w => {
          const ks = knows.filter(k => k.who === w && k.of === of)
          return <div key={w} className="idrow" data-target={`ident:${w}:${of}`}>
            <span className="idwho" style={{ color: charColour(report, w) }}>{charName(report, w)}</span>
            <span>{ks.length === 0 ? <span className="dim">knows nothing yet: no name, no pronouns</span> : ks.map((k, i) =>
              <span key={i} className={`chip id-${k.kind} ${k.right === false ? 'wrong' : ''}`}>{k.kind === 'name' ? `name “${k.v}”` : k.kind === 'pron' ? `${k.v}${k.right === false ? ' (wrong)' : ''}` : `private: ${k.v}`}</span>)}</span>
          </div>
        })}
      </div>)}
    </div> : <div className="row dim">Rebuild langlib to see who knows which names and pronouns.</div>}
    {harms.length > 0 && <><h4>Harms on record</h4><ul className="harms">{harms.map((h, i) => <li key={i} className="bad">{h}</li>)}</ul></>}
    {idEvents.length > 0 && <details><summary className="dim">{idEvents.length} identity events so far</summary>
      <ul className="carelog">{idEvents.map((e, i) => <li key={i} className={e.ok ? '' : 'bad'}><span className="dim">¶{e.para}</span> {e.e}{!e.ok && ` (refused: ${e.why})`}</li>)}</ul></details>}
  </section>
}

const ACT_WORD: Record<string, string> = { undressTop: 'undress (top)', undressBottom: 'undress (bottom)', finishInside: 'finish inside', hairPull: 'pull hair', pinDown: 'pin down' }
const actW = (x?: string) => x ? (ACT_WORD[x] ?? x) : ''

/** A scene's lanes: one per (pair, act); a bar from the first grant to a
 *  withdrawal or the scene's end; ticks for check-ins; acts as dots. */
function SceneLanes({ report, s, current, names }: { report: Report; s: Scene; current: string; names: string[] }) {
  const cols = s.paras
  const lanes = new Map<string, (CEvent & { para: string })[]>()
  for (const e of s.events) {
    if (!e.act) continue
    // one lane per giver → receiver and act: a grant (b, a) and an act (a, b) share it
    const giver = e.kind === 'grant' || e.kind === 'withdraw' ? e.a : e.b
    const doer = e.kind === 'grant' || e.kind === 'withdraw' ? e.b : e.a
    const k = `${giver}|${doer}|${e.act}`
    if (!lanes.has(k)) lanes.set(k, [])
    lanes.get(k)!.push(e)
  }
  const col = (p: string) => cols.indexOf(p)
  const W = Math.max(1, cols.length)
  const take = s.events.find(e => e.kind === 'take')
  const close = s.events.find(e => e.kind === 'close' || e.kind === 'stop')
  const here = names.indexOf(current)
  const inScene = cols.includes(current)
  return <div className="scene">
    <div className="row"><b>¶{cols[0]}{cols.length > 1 ? `–${cols[cols.length - 1]}` : ''}</b>
      {take && <> · {charName(report, take.a)} takes {charName(report, take.b)}{take.limits?.length ? <>; <b>limits: {take.limits.map(actW).join(', ')}</b></> : '; no limits named'}</>}
      {close && <> · ends: {close.kind === 'stop' ? `${charName(report, close.a)} stops it` : `closed${close.signal === 'care' ? ' with aftercare' : ''}`}</>}
      {!inScene && here >= 0 && <span className="dim"> · {names.indexOf(cols[0]) > here ? 'later' : 'earlier'}</span>}
    </div>
    <div className="clanes">{[...lanes].map(([k, es]) => {
      const [giver, doer, act] = k.split('|')
      const grants = es.filter(e => e.kind === 'grant')
      const withdraw = es.find(e => e.kind === 'withdraw')
      const start = grants.length ? col(grants[0].para) : -1
      const end = withdraw ? col(withdraw.para) : W - 1
      const assumed = es.filter(e => e.status === 'assumed')
      const refused = es.filter(e => e.status === 'no')
      const once = grants.some(g => g.once)
      const state = withdraw ? 'withdrawn' : grants.length ? (once ? 'granted once' : `granted (${[...new Set(grants.map(g => g.signal))].join(', ')})`) : assumed.length ? 'never granted: assumed' : es.some(e => e.kind === 'ask') ? 'asked' : es.some(e => e.kind === 'wish') ? 'wished, not asked' : 'acted'
      return <React.Fragment key={k}>
        <div className="cl" data-target={`consent:${giver}:${doer}:${act}`}>
          <b>{actW(act)}</b> <span className="dim">{charName(report, giver)} → {charName(report, doer)}</span>
          <div className={`cstate ${withdraw ? 'off' : refused.length ? 'bad' : assumed.length ? 'warn' : grants.length ? 'ok' : ''}`}>{state}</div>
          {[...assumed, ...refused].slice(0, 2).map((e, i) => <div key={i} className="cwhy">¶{e.para}: {e.why}</div>)}
        </div>
        <svg className="cb" viewBox={`0 0 ${W * 12} 14`} preserveAspectRatio="none" aria-label={`${actW(act)}: ${state}`}>
          {start >= 0 && <rect x={start * 12} y={4} width={(end - start + 1) * 12} height={6} className={`cbar ${withdraw ? 'off' : ''}`} />}
          {withdraw && <rect x={end * 12 + 10} y={1} width={2.5} height={12} className="ccap" />}
          {es.filter(e => e.kind === 'checkIn').map((e, i) => <line key={i} x1={col(e.para) * 12 + 6} x2={col(e.para) * 12 + 6} y1={2} y2={12} className="ctick" ><title>check-in</title></line>)}
          {es.filter(e => e.kind === 'act').map((e, i) => <circle key={i} cx={col(e.para) * 12 + 6} cy={7} r={2.2} className={`cact st-${e.status}`}><title>{`¶${e.para}: ${e.raw}${e.why ? ` (${e.why})` : ''}`}</title></circle>)}
          {inScene && <line x1={col(current) * 12 + 6} x2={col(current) * 12 + 6} y1={0} y2={14} className="ccur" />}
        </svg>
      </React.Fragment>
    })}</div>
  </div>
}

function Consent({ report, c, current }: { report: Report; c: ConsentReport; current: number }) {
  const scenes = consentScenes(c)
  const names = report.paragraphs.map(p => p.name)
  const cur = names[current] ?? ''
  return <section><h3>Consent <span className={`badge ${c.valid ? 'valid' : c.plausible ? 'plausible' : 'failing'}`}>{c.valid ? 'valid' : c.plausible ? `plausible under ${c.assumptions.length} assumptions` : 'failing'}</span>
    {c.cared && <span className="badge valid">aftercare given</span>}</h3>
    <div className="row dim">Each lane: an act between two people. Bar: granted from that paragraph to a withdrawal (end cap) or the scene's end. Short tick: a check-in. Dot: the act (hollow: assumed). Dashed line: the current paragraph. Every state is also written out.</div>
    {c.relations.map(r => <div key={r.pair} className="row">{r.pair.split(' ').map(x => charName(report, x)).join(' and ')}: {r.kinds.join(', ') || 'no relation yet'}{r.pending.length > 0 && <span className="dim"> · proposed: {r.pending.join(', ')}</span>}</div>)}
    {c.firsts.length > 0 && <div className="row dim">firsts: {c.firsts.map(f => { const [w, x] = f.split(' '); return `${charName(report, w)} ${actW(x)}` }).join(', ')}</div>}
    {scenes.map((s, i) => <SceneLanes key={i} report={report} s={s} current={cur} names={names} />)}
  </section>
}

export function WorldView({ report, readings, current }: { report: Report; readings: Readings | null; current: number }) {
  if (!readings) return <div className="storyview dim">Reading ties, care, identity and consent…</div>
  if (readings.error) return <div className="storyview bad">{readings.error}</div>
  const ext = readings.ext && !readings.ext.error ? readings.ext : null
  const i = Math.max(0, current)
  const issues = ext?.paragraphs[i]?.issues ?? []
  const has = ext || readings.consent
  return <div className="storyview world">
    {!has && <section className="dim">This story has no ties, care, identity or consent reading (story.json "ext", events.json "consent").</section>}
    {readings.ext?.error && <pre className="err">{readings.ext.error}</pre>}
    {ext && <>
      <section><h3>Ties, care and identity <span className={`badge ${ext.valid ? 'valid' : 'failing'}`}>{ext.valid ? 'valid' : 'issues'}</span></h3>
        {issues.length > 0 && <details><summary className="bad">{issues.length} issue{issues.length > 1 ? 's' : ''} in ¶{ext.paragraphs[i]?.name}</summary>
          <ul className="harms">{issues.map((x, k) => <li key={k} className="bad">{x}</li>)}</ul></details>}
      </section>
      <TiesAffect report={report} ext={ext} current={i} />
      <Care report={report} ext={ext} current={i} />
      <Identity report={report} ext={ext} current={i} />
    </>}
    {readings.consent && !readings.consent.error && <Consent report={report} c={readings.consent} current={i} />}
  </div>
}
