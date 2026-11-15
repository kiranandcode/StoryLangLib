import React from 'react'
import type { Completeness, Report } from './types'

/** Completeness in the Studio: each clause of a paragraph with the judgements that tie it to the
 *  world, the connectives between clauses with their verdict, and what the checker objects to. */

export const KIND_LABEL: Record<string, string> = {
  event: 'event', claim: 'claim', content: 'content', goal: 'goal', act: 'gesture',
  speech: 'speech', hypothetical: 'hypothetical', external: 'Nen move',
}

const REL_LABEL: Record<string, string> = {
  cause: 'cause', effect: 'cause', purpose: 'purpose', after: 'after', before: 'before',
  during: 'at the same time', concession: 'both hold', condition: 'hypothetical',
}

export function compOf(report: Report, name: string): Completeness | undefined {
  return report.completeness?.find(c => c.name === name)
}

/** Tokens the checker objects to (its messages name them as "(token N)"). */
export function badTokens(c: Completeness): Set<number> {
  const out = new Set<number>()
  for (const i of c.issues) for (const m of i.matchAll(/\(token (\d+)\)/g)) out.add(Number(m[1]))
  return out
}

export interface TokJudgement {
  clause?: { w: string; neg: boolean; modal: boolean; quoted: boolean }
  judges: { kind: string; text: string; gloss: string }[]
  link?: { word: string; rel: string; ok: boolean; a: string; b: string }
  bad: boolean
}

/** What completeness says about each token of a paragraph. */
export function byToken(c: Completeness): Map<number, TokJudgement> {
  const bad = badTokens(c)
  const word = (t: number) => c.clauses.find(x => x.at === t)?.w ?? `token ${t}`
  const m = new Map<number, TokJudgement>()
  const get = (t: number) => { if (!m.has(t)) m.set(t, { judges: [], bad: bad.has(t) }); return m.get(t)! }
  for (const cl of c.clauses) get(cl.at).clause = cl
  for (const j of c.judges) get(j.at).judges.push(j)
  for (const l of c.links) if (l.a !== l.b)
    get(l.at).link = { word: l.word, rel: l.rel, ok: !bad.has(l.at), a: word(l.a), b: word(l.b) }
  return m
}

/** Clause heads along a line, a dot per judgement, connectives as arcs between clauses. */
function Arcs({ c }: { c: Completeness }) {
  const bad = badTokens(c)
  const clauses = [...c.clauses].sort((x, y) => x.at - y.at)
  const step = 66, pad = 30
  const x = (t: number) => pad + Math.max(0, clauses.findIndex(cl => cl.at === t)) * step
  const links = c.links.filter(l => l.a !== l.b)
  const maxSpan = Math.max(1, ...links.map(l => Math.abs(x(l.a) - x(l.b))))
  const arcH = Math.min(46, 14 + maxSpan * 0.16)
  const width = pad * 2 + Math.max(0, clauses.length - 1) * step
  const base = arcH + 16
  const height = base + 34
  return (
    <div className="jarcs-wrap">
      <svg className="jarcs" width={width} height={height}>
        {links.map((l, i) => {
          const xa = x(l.a), xb = x(l.b), mid = (xa + xb) / 2
          const h = 10 + Math.abs(xb - xa) * 0.16
          const ok = !bad.has(l.at)
          return (
            <g key={i} className={`jlink r-${l.rel} ${ok ? 'ok' : 'bad'}`}>
              <path d={`M ${xa} ${base - 12} Q ${mid} ${base - 12 - 2 * h} ${xb} ${base - 12}`} markerEnd="url(#jarrow)" />
              <text x={mid} y={base - 14 - h} textAnchor="middle">{l.word} {ok ? '✓' : '✗'}</text>
              <title>{`'${l.word}': ${REL_LABEL[l.rel] ?? l.rel}, from “${clauses.find(cl => cl.at === l.a)?.w}” to “${clauses.find(cl => cl.at === l.b)?.w}”${ok ? '' : ' — refused'}`}</title>
            </g>)
        })}
        <defs><marker id="jarrow" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="6" markerHeight="6" orient="auto">
          <path d="M0,0 L8,4 L0,8 z" className="jarrowhead" /></marker></defs>
        {clauses.map(cl => {
          const js = c.judges.filter(j => j.at === cl.at)
          return (
            <g key={cl.at} className={`jclause ${bad.has(cl.at) || js.length === 0 ? 'bad' : ''}`} data-target={`tok:${c.name}:${cl.at}`}>
              <text x={x(cl.at)} y={base} textAnchor="middle" className="w">{cl.w}</text>
              {(js.length ? js : [{ kind: 'missing', text: 'no judgement', gloss: 'no judgement' }]).map((j, k) => (
                <circle key={k} cx={x(cl.at) + (k - (Math.max(js.length, 1) - 1) / 2) * 9} cy={base + 11} r={3.4}
                  className={`jdot k-${j.kind}`}><title>{`${KIND_LABEL[j.kind] ?? j.kind}: ${j.gloss}`}</title></circle>))}
            </g>)
        })}
      </svg>
    </div>
  )
}

export function JudgementSection({ c }: { report: Report; c: Completeness }) {
  const bad = badTokens(c)
  const clauses = [...c.clauses].sort((x, y) => x.at - y.at)
  return (
    <div className="judge-sec">
      <div className={`row ${c.issues.length ? 'bad' : 'ok'}`}>
        {c.issues.length ? `${c.issues.length} objection${c.issues.length > 1 ? 's' : ''}` : `complete: ${clauses.length} clauses, each judged by the world`}
      </div>
      <Arcs c={c} />
      <ul className="jlist">{clauses.map(cl => {
        const js = c.judges.filter(j => j.at === cl.at)
        return (
          <li key={cl.at} className={bad.has(cl.at) || js.length === 0 ? 'bad' : ''} data-target={`tok:${c.name}:${cl.at}`}>
            <b className="jw">{cl.w}</b>
            {cl.neg && <span className="jflag">not</span>}{cl.modal && <span className="jflag">modal</span>}{cl.quoted && <span className="jflag">quoted</span>}
            {js.length === 0 && <span className="jchip k-missing">no judgement</span>}
            {js.map((j, k) => <span key={k} className={`jchip k-${j.kind}`} title={j.text}>
              <i>{KIND_LABEL[j.kind] ?? j.kind}</i> {j.kind === 'event' || j.kind === 'content' || j.kind === 'goal' ? j.gloss : j.text}</span>)}
          </li>)
      })}</ul>
      {c.issues.map((i, k) => <div key={k} className="row bad jissue">✗ {i}</div>)}
    </div>
  )
}
