// Parsing the readings' compact strings (ext ties, feels, needs; consent events)
// into rows the views can draw. The strings are Studio/Ext.lean's and
// Studio/Consent.lean's own; nothing here judges, it only reads.
import type { ConsentReport, ExtReport, Report } from './types'

export interface Tie { a: string; rel: string; b: string; n: number }
export interface Feel { who: string; emo: string; n: number }

export function parseTie(s: string): Tie | null {
  const m = s.match(/^(\S+) (\S+) (\S+) (\d+)$/)
  return m ? { a: m[1], rel: m[2], b: m[3], n: Number(m[4]) } : null
}
export function parseFeel(s: string): Feel | null {
  const m = s.match(/^(\S+) (\S+) (\d+)$/)
  return m ? { who: m[1], emo: m[2], n: Number(m[3]) } : null
}
export function parseNeeds(s: string): { who: string; needs: string[] } | null {
  const m = s.match(/^(\S+): (.*)$/)
  return m ? { who: m[1], needs: m[2].split(', ').filter(Boolean) } : null
}

/** One consent event, read off its line ("grant remy robin kiss verbal once"). */
export interface CEvent {
  kind: string
  a: string
  b: string
  act?: string
  signal?: string
  once?: boolean
  limits?: string[]
  status: 'yes' | 'no' | 'assumed'
  why?: string
  raw: string
}

const CONSENT_KINDS = new Set(['ask', 'grant', 'withdraw', 'stop', 'offer', 'take', 'command', 'checkIn', 'act', 'close', 'wish'])

export function parseConsent(raw: string, status: CEvent['status'], why?: string): CEvent {
  const w = raw.trim().split(/\s+/)
  const [kind, a = '', b = ''] = w
  const ev: CEvent = { kind, a, b, status, why, raw }
  if (!CONSENT_KINDS.has(kind)) return ev   // relation events: propose, consummate, ...
  if (['ask', 'withdraw', 'checkIn', 'act', 'wish'].includes(kind)) ev.act = w[3]
  if (kind === 'grant') { ev.act = w[3]; ev.signal = w[4]; ev.once = w[5] === 'once' }
  if (kind === 'take') ev.limits = w.slice(3)
  if (kind === 'close') ev.signal = w[3]
  return ev
}

/** The consent reading as a list of scenes: runs of paragraphs between an
 *  `offer`/first `grant` and a `close`/`stop`, so limits, check-ins and
 *  withdrawals read in their scene. */
export interface Scene { paras: string[]; events: (CEvent & { para: string })[] }
export function consentScenes(c: ConsentReport): Scene[] {
  const scenes: Scene[] = []
  let cur: Scene | null = null
  for (const p of c.paragraphs) {
    for (const e of p.events) {
      const ev = { ...parseConsent(e.e, e.status, e.why), para: p.name }
      if (!cur) { cur = { paras: [], events: [] }; scenes.push(cur) }
      if (!cur.paras.includes(p.name)) cur.paras.push(p.name)
      cur.events.push(ev)
      if (ev.kind === 'close' || ev.kind === 'stop') cur = null
    }
  }
  return scenes
}

/** The ext reading's per-paragraph state, aligned to the story's paragraphs. */
export function extAt(ext: ExtReport | null | undefined, name: string) {
  return ext?.paragraphs.find(p => p.name === name)
}

/** Series of a tie or feeling across the story (0 where absent). */
export function tieSeries(ext: ExtReport, key: (t: Tie) => boolean): number[] {
  return ext.paragraphs.map(p => p.ties.map(parseTie).find(t => t && key(t))?.n ?? 0)
}
export function feelSeries(ext: ExtReport, who: string, emo: string): number[] {
  return ext.paragraphs.map(p => p.feels.map(parseFeel).find(f => f && f.who === who && f.emo === emo)?.n ?? 0)
}

export const nameOf = (report: Report | null, id: string) => report?.characters.find(c => c.id === id)?.name ?? id
