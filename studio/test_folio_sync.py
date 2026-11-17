"""folio_sync.py against a fake folio relay (the routes of docs/folio.md section 1).

    python3 -m unittest studio/test_folio_sync.py
"""
from __future__ import annotations

import json
import sys
import tempfile
import threading
import unittest
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

sys.path.insert(0, str(Path(__file__).resolve().parent))
import folio_sync  # noqa: E402
import request_log  # noqa: E402


class FakeRelay(ThreadingHTTPServer):
    """In-memory relay: library, append-only comments and replies with a seq."""

    def __init__(self):
        super().__init__(("127.0.0.1", 0), Handler)
        self.library, self.puts = None, 0
        self.comments: list[dict] = []
        self.replies: list[dict] = []
        self.lock = threading.Lock()

    def add_comment(self, c: dict) -> None:
        with self.lock:
            if all(x["cid"] != c["cid"] for x in self.comments):
                self.comments.append(c | {"seq": len(self.comments) + 1})


class Handler(BaseHTTPRequestHandler):
    server: FakeRelay

    def log_message(self, *a):
        pass

    def _send(self, code: int, body) -> None:
        raw = json.dumps(body).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(raw)))
        self.end_headers()
        self.wfile.write(raw)

    def _body(self):
        return json.loads(self.rfile.read(int(self.headers["Content-Length"])))

    def do_GET(self):
        u = urlparse(self.path)
        since = int(parse_qs(u.query).get("since", ["0"])[0])
        s = self.server
        if u.path == "/v1/health":
            return self._send(200, {"ok": True})
        if u.path == "/v1/library":
            return self._send(200, s.library) if s.library else self._send(404, {})
        if u.path == "/v1/comments":
            with s.lock:
                return self._send(200, {"comments": [c for c in s.comments if c["seq"] > since], "seq": len(s.comments)})
        if u.path == "/v1/replies":
            with s.lock:
                return self._send(200, {"replies": [r for r in s.replies if r["seq"] > since], "seq": len(s.replies)})
        self._send(404, {})

    def do_PUT(self):
        if self.path != "/v1/library":
            return self._send(404, {})
        self.server.library = self._body()
        self.server.puts += 1
        self._send(200, {"ok": True})

    def do_POST(self):
        s = self.server
        if self.path == "/v1/comments":
            s.add_comment(self._body())
            return self._send(200, {"ok": True})
        if self.path == "/v1/replies":
            with s.lock:
                seen = {(r["cid"], r["status"], r["at"]) for r in s.replies}
                for r in self._body():
                    if (r["cid"], r["status"], r["at"]) not in seen:
                        s.replies.append(r | {"seq": len(s.replies) + 1})
            return self._send(200, {"ok": True})
        self._send(404, {})


def write_story(d: Path, paras: list[str], *, meta=None, story=None, flat=False) -> None:
    pd = d if flat else d / "paragraphs"
    pd.mkdir(parents=True)
    for i, t in enumerate(paras, 1):
        (pd / f"{i:02d}.txt").write_text(t + "\n")
        (pd / f"{i:02d}.json").write_text("{}")  # annotations are not paragraphs
    (d / "meta.json").write_text(json.dumps(meta or {}))
    (d / "story.json").write_text(json.dumps(story or {}))


class FolioSyncTest(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.stories = self.tmp / "stories"
        self.state = self.tmp / "folio-sync.json"
        self._log = request_log.LOG
        request_log.LOG = self.tmp / "requests.jsonl"
        # a series whose chain order (c3 after c1, c2 after c3) differs from name order
        sd = self.stories / "series"
        write_story(sd, [], meta={"series": "a test series"}, story={"title": "Series"})
        (sd / "chapters").mkdir()
        for stem in ("v1c01", "v1c02", "v2c03"):
            (sd / "chapters" / f"{stem}.json").write_text('{"outline": []}')
        write_story(self.stories / "series-v1c01", ["One.", "* * *", "Two."],
                    meta={"series": "x", "chapter": "v1c01: Start"})
        write_story(self.stories / "series-v2c03", ["Three."],
                    meta={"series": "x", "chapter": "v2c03: Turn"}, story={"after": "series-v1c01"})
        write_story(self.stories / "series-v1c02", ["Four."],
                    meta={"series": "x", "chapter": "v1c02"}, story={"after": "series-v2c03"})
        write_story(self.stories / "lone", ["Alone."], story={"title": "Lone"}, flat=True)
        self.names = ["series", "lone", "missing"]
        self.relay = FakeRelay()
        threading.Thread(target=self.relay.serve_forever, daemon=True).start()
        self.client = folio_sync.Relay(f"http://127.0.0.1:{self.relay.server_address[1]}", timeout=5)

    def tearDown(self):
        self.relay.shutdown()
        self.relay.server_close()
        request_log.LOG = self._log

    def round(self):
        return folio_sync.sync_round(self.client, self.stories, self.state, self.names)

    def comment(self, cid: str, text: str, para="01"):
        self.relay.add_comment({"cid": cid, "book": "series", "chapter": "series-v1c01", "para": para,
                                "para_sha": "", "start": 0, "end": 3, "quote": "One", "text": text,
                                "created_at": "2026-11-17T12:00:00Z"})

    def test_library_shape_and_order(self):
        lib = folio_sync.build_library(self.stories, self.names)
        self.assertEqual([b["id"] for b in lib["books"]], ["series", "lone"])
        series, lone = lib["books"]
        self.assertEqual(series["title"], "Series")
        self.assertEqual([c["id"] for c in series["chapters"]], ["series-v1c01", "series-v2c03", "series-v1c02"])
        self.assertEqual([c["title"] for c in series["chapters"]],
                         ["Volume 1, Chapter 1: Start", "Volume 2, Chapter 3: Turn", "Volume 1, Chapter 2"])
        first = series["chapters"][0]
        self.assertEqual((first["volume"], first["number"]), (1, 1))
        self.assertEqual([p["n"] for p in first["paragraphs"]], ["01", "02", "03"])
        self.assertEqual(first["paragraphs"][1]["text"], "* * *")
        self.assertEqual(first["sha"], folio_sync.sha("One.\n\n* * *\n\nTwo."))
        self.assertEqual(lone["title"], "Lone")
        self.assertEqual([c["id"] for c in lone["chapters"]], ["lone"])
        # the version ignores generated_at
        self.assertEqual(folio_sync.build_library(self.stories, self.names)["version"], lib["version"])

    def test_library_pushed_only_when_changed(self):
        self.assertTrue(self.round()["library"])
        self.assertFalse(self.round()["library"])
        self.assertEqual(self.relay.puts, 1)
        (self.stories / "lone" / "02.txt").write_text("More.")
        self.assertTrue(self.round()["library"])
        self.assertEqual(self.relay.puts, 2)
        self.assertEqual(len(self.relay.library["books"][1]["chapters"][0]["paragraphs"]), 2)

    def test_comments_become_requests_and_replies_flow_back(self):
        self.comment("c1", "make this sharper")
        self.comment("c2", "   ")  # empty: skipped, not filed
        r = self.round()
        self.assertEqual(r["comments"], 1)
        reqs = request_log.all_requests()
        self.assertEqual(len(reqs), 1)
        req = reqs[0]
        self.assertEqual((req["kind"], req["story"], req["para"], req["quote"], req["text"], req["target"]),
                         ("story", "series-v1c01", "01", "One", "make this sharper", "folio"))
        self.assertEqual(json.loads(self.state.read_text())["map"], {"c1": req["id"]})
        self.assertEqual([(x["cid"], x["status"], x["reply"]) for x in self.relay.replies], [("c1", "open", None)])

        # nothing new: no duplicate request, no reply posted
        self.assertEqual(self.round(), {"library": False, "comments": 0, "replies": 0})
        self.assertEqual(len(request_log.all_requests()), 1)

        request_log.claim("agent")
        request_log.set_status(req["id"], "done", reply="sharpened it", by="agent")
        self.assertEqual(self.round()["replies"], 1)
        last = self.relay.replies[-1]
        self.assertEqual((last["rid"], last["status"], last["reply"], last["by"]), (req["id"], "done", "sharpened it", "agent"))
        self.assertTrue(last["at"].endswith("Z"))

    def test_a_crashed_state_does_not_refile(self):
        self.comment("c1", "one")
        self.round()
        s = json.loads(self.state.read_text())
        s["since"] = 0  # the relay replays everything
        self.state.write_text(json.dumps(s))
        self.round()
        self.assertEqual(len(request_log.all_requests()), 1)


if __name__ == "__main__":
    unittest.main()
