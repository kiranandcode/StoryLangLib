// Shapes of `langlib story <dir>` (LangLib/Studio/Report.lean) plus what the server adds.

export type Tri = 'yes' | 'no' | 'unknown'

export interface Token {
  w: string
  p: string
  ent?: string
  mk?: 'pron' | 'name'
  phora?: string
  mstart?: boolean
  spk?: string
  clause?: boolean
  time?: boolean
}

export interface CheckReport {
  ok: boolean
  edits: string[]
  refIssues: string[]
  badLeaves: string[]
  editCount: number
}

export interface DocLayer {
  check: CheckReport
  tokens: Token[]
  entities: { id: string; name: string; kind: string }[]
  clauses: { verb: string; at: number; subj: string; obj: string; embedded: boolean; advs: string[] }[]
}

export interface EventRow {
  e: string
  gloss: string
  src: string
  at: number | null
  phase: 'main' | 'meanwhile' | 'flashback'
  parties: string[]
  status: Tri
  why: string
  unmotivated: boolean
  motive: string
  time: [number, number] | null
}

export interface Explain {
  lit: string
  src: string
  reasons: [string, number][]
  strength: number
  attitude: string
  status: string
  caught: boolean
}

export interface BeliefDelta {
  who: string
  change: 'gained' | 'lost'
  lit: string
  gloss: string
  false: boolean
  explain: Explain[]
}

export interface Delta {
  moves: { who: string; from: string; to: string; assumed: boolean }[]
  objects: { what: string; now: { heldBy?: string; place?: string } }[]
  beliefs: BeliefDelta[]
  nested: { who: string; about: string; lit: string; gloss: string; accurate: boolean }[]
  bonds: { from: string; to: string; dim: string; before: number; after: number }[]
  consentGiven: string[]
  consentWithdrawn: string[]
  goals: { who: string; goal: string }[]
}

export interface Lit { lit: string; gloss: string; true: boolean }

export interface State {
  at: Record<string, { place: string; known: boolean }>
  objects: Record<string, { heldBy?: string; place?: string; known: boolean }>
  views: Record<string, Lit[]>
  bonds: Record<string, Record<string, number>>
  consent: string[]
  goals: Record<string, string[]>
  plans: Record<string, { goal: string; next: string[] }[]>
  promises: { by: string; to: string; lit: string; kept: boolean }[]
  questions: string[]
}

export interface Paragraph {
  name: string
  text: string
  beat: string | null
  errors: string[]
  doc: DocLayer | null
  lexicon: { at: number; verb: string; e: string; asserted: boolean }[]
  events: EventRow[]
  verdict: 'valid' | 'plausible' | 'failing'
  assumptions: { e: string; why: string }[]
  retro: { i: number; status: Tri; why: string }[]
  claims: { claim: string; holds: boolean; error?: string }[]
  realisation: { planned: string[]; missing: string[]; extra: string[]; realises: boolean } | null
  delta: Delta
  state: State
  freshness?: { status: 'none' | 'unstamped' | 'fresh' | 'stale'; why: string[]; sha: string }
}

export interface Character { id: string; name: string; pron: string; traits: string[]; values: string[] }

export interface Theorem { line: number; statement: string; ok?: boolean; error?: string }

export interface Proofs {
  status: 'none' | 'running' | 'ok' | 'failed' | 'error'
  secs?: number
  theorems?: Record<string, Theorem>
  errors?: string[]
  guards?: string[]
  error?: string
  file?: string
  at?: number
}

export interface Beats {
  conds: string[]
  vocab: { id: string; label: string; pre: string[]; add: string[]; keys: string[] }[]
  story: string[]
  valid: boolean
  failure: { i: number; why: string } | null
  abstracted: string[]
  refines: boolean
}

export interface Report {
  name: string
  title: string
  error?: string
  secs: number
  characters: Character[]
  places: string[]
  objects: string[]
  atoms: { id: string; label: string; truth: boolean }[]
  start: State
  startLine: Record<string, { place: string; known: boolean }>
  storyline: Record<string, { place: string; known: boolean }>[]
  paragraphs: Paragraph[]
  time: { consistent: boolean; toldOrder: boolean; constraints: number }
  verdict: { valid: boolean; plausible: boolean; assumptions: number; failure: { i: number; why: string } | null }
  beats: Beats | null
  proofs: Proofs
  meta?: Record<string, unknown>
  summary?: Record<string, unknown>
}

export type RequestStatus = 'open' | 'claimed' | 'working' | 'done' | 'declined'
export interface StudioRequest {
  id: string
  kind: 'story' | 'tool'
  story: string
  para: string
  quote: string
  text: string
  at: number
  status: RequestStatus
  reply?: string
  updated?: number
  history: { status: RequestStatus; reply?: string; by?: string; at: number }[]
  checks?: { check: string; ok: boolean; detail: string[] }[] | null
}
