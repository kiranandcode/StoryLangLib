# Folio: a story reader for the Flip 8

Folio (`me.kirancodes.folio`) is an Android app for reading StoryLangLib stories on
Kiran's Galaxy Z Flip 8. Comments she leaves on a passage become Studio requests,
so the agents serving `studio_mcp.py await_request` act on them and their replies
show up in the app.

Three pieces, each built separately against the protocol below.

```
Mac (langlib)                 vibux (Framework)                 Flip 8
studio/folio_sync.py  <-->  folio-relay (NixOS service)  <-->  Folio app
 reads stories/, writes      stores the library bundle,       reads offline,
 studio/requests.jsonl       comments and replies             bookmarks locally
```

Kiran chose (2026-11-17): the Flip 8 app ships through the vibux deployer like
henshin, and vibux relays the text, so the private chapters are stored on vibux.

## 1. folio-relay on vibux

A small Python service (stdlib only) in the vibux repo, `pkgs/folio-relay/` plus
`modules/folio-relay.nix`, listening on vibux's Tailscale address, port 7481.
State lives in `/var/lib/folio-relay/` (mode 0700, its own user).

Every request is pinned with `tailscale whois` to a node StableID from
`keys/relay/devices.nix`, the same way the mailbox pins the phone. The Mac (`mac-air`)
and the phone (`phone`) get different routes; anyone else gets 403.

| Route | Who | Body |
|---|---|---|
| `PUT /v1/library` | Mac | the library bundle (below), replaces the stored one |
| `GET /v1/library` | phone | the bundle; honours `If-None-Match` with its `version` as ETag |
| `POST /v1/comments` | phone | one comment; idempotent on `cid` |
| `GET /v1/comments?since=N` | Mac | comments with `seq > N`, plus `seq` |
| `POST /v1/replies` | Mac | a list of reply records; idempotent on `(cid, status, at)` |
| `GET /v1/replies?since=N` | phone | reply records with `seq > N` |
| `GET /v1/health` | both | `{"ok":true}` |

Bodies are JSON, capped at 32 MiB for the library and 64 KiB otherwise. Writes go to a
temp file and are renamed into place; comments and replies are append-only JSONL with
a monotonically increasing `seq`.

## 2. The library bundle

```json
{
  "version": "sha256 of the canonical {books} (generated_at left out)",
  "generated_at": "2026-11-17T12:00:00Z",
  "books": [
    {
      "id": "private-fixpoint",
      "title": "Fixpoint",
      "chapters": [
        {
          "id": "private-fixpoint-v1c01",
          "title": "Volume 1, Chapter 1",
          "volume": 1, "number": 1,
          "sha": "sha256 of the chapter's paragraph texts joined",
          "paragraphs": [ { "n": "01", "sha": "...", "text": "..." } ]
        }
      ]
    }
  ]
}
```

A series (a dir with `chapters/` and `meta.json` naming the `series`) is one book whose
chapters are its chained chapter dirs, in order: `<series>-<stem>` for each
`chapters/<stem>.json`, ordered by their `story.json` `after` links. A chapter's title
comes from its `meta.json` `chapter` (`"v1c03: Name"` gives "Volume 1, Chapter 3: Name");
a book's title is its `story.json` `title`. Any other story dir is a book with one
chapter. Only paragraphs whose `NN.txt` exists are included. Scene breaks are paragraphs
whose text is exactly `* * *`.

## 3. Comments and replies

A comment, as the phone posts it:

```json
{
  "cid": "uuid4 made on the phone",
  "book": "private-fixpoint",
  "chapter": "private-fixpoint-v1c03",
  "para": "07",
  "para_sha": "sha of the paragraph the quote was taken from",
  "start": 120, "end": 188,
  "quote": "the selected text, may be empty",
  "text": "Kiran's comment",
  "created_at": "2026-11-17T12:00:00Z"
}
```

`folio_sync.py` turns each new comment into a Studio request with
`request_log.py` (`kind: "story"`, `story: <chapter>`, `para`, `quote`, `text`,
`target: "folio"`) and keeps the map `cid -> request id` in
`studio/folio-sync.json` (gitignored), saved after each comment so a comment is never
filed twice. Empty comments are skipped. Whenever a mapped request's folded state
changes, including the first `open`, it posts:

```json
{ "cid": "...", "rid": "...", "status": "open|claimed|working|done|declined",
  "reply": "agent's reply text or null", "by": "...", "at": "..." }
```

## 4. folio_sync.py on the Mac

`python3 studio/folio_sync.py [--once] [--interval 30]`, started from a terminal or the
Cove (launchd can't read `~/Documents` under TCC). Each round it:

1. builds the bundle from `stories/` (books listed in `studio/folio-books.json`,
   default: every `private-fixpoint-*` chapter as the Fixpoint book) and PUTs it if
   `version` changed;
2. pulls new comments and files them as requests;
3. pushes status changes of mapped requests.

The relay URL comes from `FOLIO_RELAY` (default `http://100.107.43.4:7481`). It never
touches story files and prints counts only. `studio/test_folio_sync.py` runs it against
an in-memory fake relay (`python3 -m unittest studio/test_folio_sync.py`).

## 5. The app

Kotlin and Jetpack Compose, minSdk 34, built on aws-dev the way henshin is, as an
unsigned non-debuggable release APK, then shipped with
`mac/vibux-app-release folio` (signed with the Approver release key) and installed from
the approver's Folio card.

- **Library**: books, chapters in order, per-chapter progress, an *updated* dot when a
  chapter's `sha` changed since she last read it, and a list of changed paragraphs.
- **Reader**: one chapter as a continuous scroll, typography from `docs/ui-reading.md`
  (Literata 20sp, 1.6 leading, about 66ch, 1.5em indents, asterism scene breaks; light
  `#2b2622` on `#fbf8f2`, sepia, dark `#d9d2c5` on `#1b1a18`), A-/A+, volume keys page,
  keep screen on. Resumes at the exact paragraph and offset.
- **Bookmarks and highlights**: long-press a selection for Highlight (four colours),
  Bookmark, Comment, Copy. A Saved screen lists bookmarks, highlights and favourite
  passages. Anchors are `(chapter, para, start, end, para_sha, quote)`; when the
  paragraph's sha changes, re-anchor by finding the quote, else mark the anchor
  stale.
- **Comments**: the comment sheet shows the quote, a text field, and send. Comments are
  queued in Room and sent when vibux is reachable. Each paragraph with comments has a
  margin mark; tapping it shows the thread with status chips (queued, open, working,
  done, declined) and the agent's reply.
- **Privacy**: `FLAG_SECURE` on every window, a biometric lock on open and after
  5 minutes in the background, and nothing shown on the cover screen or lock-screen
  notifications beyond "Folio".
- **Sync**: on open, on pull-to-refresh, and every 15 minutes with WorkManager while
  on Tailscale. Everything works offline from the last bundle.
- **Flip**: Flex mode (half-folded) puts the text on the top half and the controls on
  the bottom.

Local state (bookmarks, highlights, positions, settings) lives only on the phone in
v1.
