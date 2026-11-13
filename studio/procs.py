"""Subprocesses that cannot outlive the Studio.

Every child (langlib, lake build, lake env lean, story-lean) starts in its own
process group under `nice -n 10`, with a timeout. On timeout, cancellation,
server reload or shutdown the whole group gets SIGTERM, then SIGKILL. Live
groups are recorded in `studio/.pgids` so a worker that was killed outright is
cleaned up by the next one (`reap_stale`).

Lean and lake jobs take a machine-wide file lock (`.lake/studio-lean.lock`), so
the server and the workflows CLI never run two at once; langlib calls take a
second lock of their own, so at most one of each runs at any time.
"""
from __future__ import annotations

import asyncio
import contextlib
import fcntl
import os
import signal
import subprocess
import threading
import time
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LANGLIB = ROOT / ".lake/build/bin/langlib"
PGIDS = Path(__file__).resolve().parent / ".pgids"
LOCKS = {"lean": ROOT / ".lake/studio-lean.lock", "langlib": ROOT / ".lake/studio-langlib.lock"}
NICE = ["nice", "-n", "10"]

_live: set[int] = set()
_live_mu = threading.Lock()


@dataclass
class Result:
    returncode: int
    stdout: str
    stderr: str
    secs: float
    timed_out: bool = False


def kind_of(argv: list[str]) -> str:
    return "lean" if argv and Path(argv[0]).name in ("lake", "lean") else "langlib"


# ------------------------------------------------------------------ bookkeeping

def _save() -> None:
    try:
        PGIDS.write_text("".join(f"{g}\n" for g in sorted(_live)))
    except OSError:
        pass


def _track(pgid: int) -> None:
    with _live_mu:
        _live.add(pgid)
        _save()


def _untrack(pgid: int) -> None:
    with _live_mu:
        _live.discard(pgid)
        _save()


def _alive(pgid: int) -> bool:
    try:
        os.killpg(pgid, 0)
        return True
    except (ProcessLookupError, PermissionError):
        return False


def kill_group(pgid: int, grace: float = 2.0) -> None:
    """SIGTERM the group, wait up to `grace` seconds, then SIGKILL it."""
    try:
        os.killpg(pgid, signal.SIGTERM)
    except ProcessLookupError:
        _untrack(pgid)
        return
    deadline = time.time() + grace
    while time.time() < deadline and _alive(pgid):
        time.sleep(0.05)
    with contextlib.suppress(ProcessLookupError):
        os.killpg(pgid, signal.SIGKILL)
    _untrack(pgid)


def kill_all() -> None:
    with _live_mu:
        groups = list(_live)
    for g in groups:
        kill_group(g, grace=1.0)


def reap_stale() -> None:
    """Kill groups a previous (killed) server left behind."""
    if not PGIDS.exists():
        return
    for line in PGIDS.read_text().split():
        with contextlib.suppress(ValueError):
            g = int(line)
            if g not in _live and g != os.getpgid(0):
                kill_group(g, grace=1.0)
    _save()


def install_signal_handlers() -> None:
    """For plain scripts (the CLI): kill children on SIGTERM/SIGINT/SIGHUP."""
    def handler(sig, _frame):
        kill_all()
        raise SystemExit(128 + sig)
    for s in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(s, handler)


# ------------------------------------------------------------------ locks

@contextlib.contextmanager
def file_lock(kind: str):
    LOCKS[kind].parent.mkdir(parents=True, exist_ok=True)
    with open(LOCKS[kind], "a") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)


_async_locks: dict[str, asyncio.Lock] = {}


async def _acquire_file_lock(kind: str):
    """Take the file lock without blocking the event loop; cancellable."""
    LOCKS[kind].parent.mkdir(parents=True, exist_ok=True)
    f = open(LOCKS[kind], "a")
    while True:
        try:
            fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
            return f
        except BlockingIOError:
            try:
                await asyncio.sleep(0.2)
            except asyncio.CancelledError:
                f.close()
                raise


# ------------------------------------------------------------------ running

def run(argv: list[str], timeout: float = 120, cwd: Path = ROOT, input: str | None = None) -> Result:
    """Blocking run (for the CLI), under the lock for its kind."""
    with file_lock(kind_of(argv)):
        t0 = time.time()
        p = subprocess.Popen(NICE + argv, cwd=cwd, start_new_session=True, text=True,
                             stdin=subprocess.PIPE if input is not None else subprocess.DEVNULL,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        _track(p.pid)
        try:
            out, err = p.communicate(input, timeout=timeout)
            return Result(p.returncode, out, err, round(time.time() - t0, 2))
        except subprocess.TimeoutExpired:
            kill_group(p.pid)
            out, err = p.communicate()
            return Result(-9, out, err, round(time.time() - t0, 2), timed_out=True)
        except BaseException:
            kill_group(p.pid)
            raise
        finally:
            if p.poll() is not None and not _alive(p.pid):
                _untrack(p.pid)
            else:
                kill_group(p.pid)


async def arun(argv: list[str], timeout: float = 120, cwd: Path = ROOT) -> Result:
    """Async run (for the server). Cancelling the awaiting task kills the group."""
    kind = kind_of(argv)
    lock = _async_locks.setdefault(kind, asyncio.Lock())
    async with lock:
        f = await _acquire_file_lock(kind)
        try:
            t0 = time.time()
            p = await asyncio.create_subprocess_exec(
                *NICE, *argv, cwd=cwd, start_new_session=True, stdin=subprocess.DEVNULL,
                stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
            _track(p.pid)
            try:
                out, err = await asyncio.wait_for(p.communicate(), timeout)
                return Result(p.returncode, out.decode(), err.decode(), round(time.time() - t0, 2))
            except asyncio.TimeoutError:
                await asyncio.to_thread(kill_group, p.pid)
                return Result(-9, "", f"timed out after {timeout}s", round(time.time() - t0, 2), timed_out=True)
            except BaseException:
                await asyncio.shield(asyncio.to_thread(kill_group, p.pid))
                raise
            finally:
                if _alive(p.pid):
                    await asyncio.to_thread(kill_group, p.pid)
                else:
                    _untrack(p.pid)
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)
            f.close()


def langlib_argv(*args: str) -> list[str]:
    return [str(LANGLIB), *args]
