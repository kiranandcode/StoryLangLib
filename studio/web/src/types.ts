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

/** Completeness (LangLib/Studio/Complete.lean): every clause judged, connectives checked. */
export interface Completeness {
  name: string
  issues: string[]
  clauses: { at: number; w: string; span?: number[]; neg: boolean; modal: boolean; quoted: boolean; parent: number | null }[]
  links: { at: number; word: string; rel: string; a: number; b: number }[]
  judges: { at: number; kind: string; text: string; gloss: string }[]
  trees?: TreeJ[]
  derivations?: { at: number; d: Deriv }[]
}

/** The story as an argument graph (Complete.lean `argumentGraph`): facts, beliefs, sayings;
 *  support and attack edges; grounded labelling (in / out). */
export interface Argument {
  nodes: { id: string; kind: 'fact' | 'belief' | 'said'; who: string; lit: string; gloss: string; para: string; status: 'in' | 'out'; note: string; ats?: string[] }[]
  edges: { src: string; tgt: string; kind: 'support' | 'attack'; why: string }[]
}

/** Why a verdict holds: a conclusion over its premises under a named rule (Complete.lean `Deriv`). */
export interface Deriv { rule: string; concl: string; ok: boolean; prems: Deriv[] }

/** A sentence's tree as the annotation writes it: a node (`c`, `k`) or a leaf (`w`, `p`). */
export interface TreeJ { c?: string; k?: TreeJ[]; w?: string; p?: string; r?: string; ref?: string; sense?: string; spk?: string }

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
  completeness?: Completeness[]
  argument?: Argument
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

/** `langlib ext` (Studio/Ext.lean): ties, care, identity and affect per paragraph. */
export interface ExtPara {
  name: string
  events: { e: string; at: number; ok: boolean; why: string }[]
  issues: string[]
  mentions: number
  /** "a tie b n" */
  ties: string[]
  /** "c: need, need" */
  needs: string[]
  harms: string[]
  /** "c emotion n" */
  feels: string[]
  knows?: { who: string; of: string; kind: 'name' | 'pron' | 'secret'; v: string; right?: boolean }[]
}
export interface ExtReport { valid: boolean; paragraphs: ExtPara[]; error?: string }

/** `langlib consent` (Studio/Consent.lean): the refined consent reading. */
export interface ConsentReport {
  valid: boolean
  plausible: boolean
  cared: boolean
  assumptions: { i: number; why: string }[]
  firsts: string[]
  relations: { pair: string; kinds: string[]; pending: string[] }[]
  paragraphs: { name: string; events: { e: string; status: 'yes' | 'no' | 'assumed'; why?: string }[] }[]
  error?: string
}

/** `langlib style` / `house` / `academic`: named rule sets over measured features. */
export interface StyleReport {
  styles: { name: string; holds?: boolean; failing: string[]; rules: { name: string; rule: string; holds: boolean }[] }[]
  features?: Record<string, number | boolean>
  flagged?: Record<string, unknown>
  pov?: string
  error?: string
}

export interface Readings {
  name: string
  ext: ExtReport | null
  consent: ConsentReport | null
  style: StyleReport | null
  house: StyleReport | null
  error?: string
}

/** `langlib argument` (Studio/PaperArg.lean): a paper's argument graph with its grounded labelling. */
export interface PaperArgNode {
  id: string
  kind: 'claim' | 'definition' | 'lore' | 'term' | 'cite' | 'example' | 'evaluate' | 'deny' | 'concede' | 'promise' | 'contribution' | 'hedge' | 'deliver'
  t: string
  para: string
  voice: 'author' | 'prior' | 'reader' | 'data'
  note: string
  label: 'in' | 'out' | 'undec'
  held: '' | 'accepted' | "authors' word" | 'denied' | 'known'
  support: ({ src: string; for: boolean; reasons: string[]; strength: number; attitude: string } | string)[]
}
export interface PaperArg {
  valid: boolean
  coherent: boolean
  failure: { i: number; why: string } | null
  paragraphs: { name: string; moves: { i: number; move: string; t?: string; a?: string; b?: string; sec?: number; uses?: string[]; premises?: string[]; ok: boolean; why: string }[] }[]
  nodes: PaperArgNode[]
  edges: { src: string; tgt: string; kind: 'support' | 'attack' | 'contrast' | 'delivers'; why: string }[]
  gaps: { kind: string; t: string; sec?: number }[]
  deferred: { t: string; sec: number }[]
  antitheses: string[]
  contrasts: string[]
  error?: string
}
export interface Paper {
  name: string
  title: string
  paragraphs: { name: string; text: string }[]
  argument: PaperArg
  academic: StyleReport
  proved: { gaps: string[]; deferred: [string, string][]; antitheses: string[]; contrasts: string[] } | null
  error?: string
}
