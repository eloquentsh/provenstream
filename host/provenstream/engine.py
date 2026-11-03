# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""An engine process, spoken to in JSON lines (PROTOCOL.md; the messages are Provenstream/Engine/Step.lean's).

Any irregularity kills the engine and raises `EngineFailure`; nothing is stored, and the service starts a fresh engine
(which reloads streams lazily) before its next request. The process's CPU time is measured: sampled from the operating
system while it runs (`/proc` on Linux, `ps` elsewhere) and read exactly from its resource usage when it is reaped.
"""
from __future__ import annotations
import os, queue, subprocess, sys, threading, time
from typing import List, Optional

from . import wire


def process_cpu_seconds(pid: int) -> Optional[float]:
    """User plus system CPU seconds of a running process, or None when the platform does not tell."""
    try:
        with open("/proc/%d/stat" % pid) as f:
            fields = f.read().rsplit(")", 1)[1].split()
        tick = os.sysconf("SC_CLK_TCK")
        return (int(fields[11]) + int(fields[12])) / tick
    except (OSError, ValueError, IndexError):
        pass
    try:
        out = subprocess.run(["ps", "-o", "time=", "-p", str(pid)], capture_output=True, text=True, timeout=5).stdout
        t = out.strip()
        if not t:
            return None
        days = 0
        if "-" in t:
            d, t = t.split("-", 1)
            days = int(d)
        parts = [float(x) for x in t.split(":")]
        secs = 0.0
        for p in parts:
            secs = secs * 60 + p
        return days * 86400 + secs
    except (OSError, ValueError, subprocess.SubprocessError):
        return None


# The only variables an engine is given. An engine reads no environment (Provenstream/Engine/Step.lean): it needs a
# PATH to be started by name, and LEAN_ABORT_ON_PANIC, else a `panic!` prints to stderr and returns a default value.
# Nothing of the host's own is passed on: not its database URL, the PG* settings, tokens or anything else it was given.
ENGINE_ENV_PASSED = ("PATH",)


def engine_env(environ=None) -> dict:
    """The environment an engine starts with: PATH (the host's, else the system default) and LEAN_ABORT_ON_PANIC=1."""
    environ = os.environ if environ is None else environ
    env = {k: environ[k] for k in ENGINE_ENV_PASSED if environ.get(k)}
    env.setdefault("PATH", os.defpath)
    env["LEAN_ABORT_ON_PANIC"] = "1"
    return env


class EngineFailure(Exception):
    """The engine died, wrote to stderr, timed out or answered something that is not an answer."""


class EngineRefusedLog(EngineFailure):
    """The engine refused to start on the stored log: it is not Valid, or not what its requests produce."""


class Engine:
    def __init__(self, command: List[str], timeout: float = 30.0, startup_timeout: float = 120.0):
        self.command = list(command)
        self.cpu_finished = 0.0           # CPU seconds of processes already reaped (exact: their resource usage)
        self.starts = 0
        self.timeout = timeout
        self.startup_timeout = startup_timeout
        self.proc: Optional[subprocess.Popen] = None
        self.failed: Optional[str] = None
        self._out: "queue.Queue[Optional[bytes]]" = queue.Queue()
        self._err: List[str] = []

    # -- lifecycle ----------------------------------------------------------------------------------------------------

    def start(self) -> None:
        """Start an empty engine (streams are synced lazily)."""
        self.stop()
        self.failed = None
        self._out = queue.Queue()
        self._err = []
        try:
            self.proc = subprocess.Popen(self.command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                         stderr=subprocess.PIPE, env=engine_env())
        except OSError as x:              # no such file, not executable: an engine that does not start, like any other
            self.failed = "engine did not start: %s" % x
            raise EngineFailure(self.failed) from x
        self.starts += 1
        threading.Thread(target=self._read_out, args=(self.proc, self._out), daemon=True).start()
        self._err_thread = threading.Thread(target=self._read_err, args=(self.proc, self._err), daemon=True)
        self._err_thread.start()
        ready = self._next(self.startup_timeout)
        if ready != {"ready": True}:
            self._kill("engine did not start: %r" % (ready,))
            raise EngineFailure(self.failed)

    def stop(self) -> None:
        p, self.proc = self.proc, None
        if p is None:
            return
        try:
            p.stdin.close()
        except Exception:
            pass
        self._reap(p, 5.0)

    def _reap(self, p: subprocess.Popen, grace: float) -> None:
        """Wait for `p` (killing it after `grace` seconds) and add its exact CPU time (`wait4`'s resource usage)."""
        deadline = time.time() + grace
        while True:
            try:
                pid, status, ru = os.wait4(p.pid, os.WNOHANG)
            except ChildProcessError:          # already reaped by someone else: its usage is lost
                return
            if pid == p.pid:
                self.cpu_finished += ru.ru_utime + ru.ru_stime
                p.returncode = status
                return
            if time.time() > deadline:
                try:
                    p.kill()
                except OSError:
                    pass
                deadline = time.time() + 5
            time.sleep(0.01)

    def cpu_seconds(self) -> float:
        """CPU seconds of every process this engine ran: exact for the reaped ones, sampled for the running one."""
        running = 0.0
        p = self.proc
        if p is not None and self._poll(p):
            running = process_cpu_seconds(p.pid) or 0.0
        return self.cpu_finished + running

    def alive(self) -> bool:
        return self.proc is not None and self._poll(self.proc) and self.failed is None

    def _poll(self, p: subprocess.Popen) -> bool:
        """`p` is running. (Not `Popen.poll`, which would reap it without its resource usage.)"""
        if p.returncode is not None:
            return False
        try:
            pid, status, ru = os.wait4(p.pid, os.WNOHANG)
        except ChildProcessError:
            p.returncode = -1
            return False
        if pid == p.pid:
            self.cpu_finished += ru.ru_utime + ru.ru_stime
            p.returncode = status
            return False
        return True

    # -- one request --------------------------------------------------------------------------------------------------

    def _send(self, line: bytes, timeout: Optional[float] = None) -> object:
        if not self.alive():
            raise EngineFailure(self.failed or "engine not running")
        try:
            self.proc.stdin.write(line + b"\n")
            self.proc.stdin.flush()
        except (BrokenPipeError, OSError) as x:
            self._kill("engine stdin closed: %s" % x)
            raise EngineFailure(self.failed)
        answer = self._next(timeout or self.timeout)
        if self._err:
            self._kill("engine wrote to stderr: %s" % self._stderr_text())
            raise EngineFailure(self.failed)
        return answer

    def sync(self, stream: str, from_len: int, rows) -> int:
        """Append a stream's stored rows `(seq, request JSON, event JSON)` past `from_len` to the engine's log of that
        stream; answers the engine's new length. Raises `EngineRefusedLog` if the rows do not replay."""
        line = ('{"sync":{"stream_id":%s,"from":%d,"rows":[%s]}}' % (wire.dumps(stream), from_len, _rows_json(rows))).encode("utf-8")
        answer = self._send(line, self.startup_timeout)
        if isinstance(answer, dict) and answer.get("synced") == stream and isinstance(answer.get("length"), int):
            return answer["length"]
        if isinstance(answer, dict) and answer.get("error") in ("refused", "out_of_sync", "malformed"):
            raise EngineRefusedLog("stream %s: %r" % (stream, answer))
        self._kill("engine answered a sync with %r" % (answer,))
        raise EngineFailure(self.failed)

    def load(self, stream: str, k: int, state: dict) -> None:
        """Set a stream from a snapshot (the service verifies it first)."""
        answer = self._send(wire.dumps({"load": {"stream_id": stream, "k": k, "state": state}}).encode("utf-8"))
        if answer != {"loaded": stream, "length": k}:
            raise EngineRefusedLog("stream %s: snapshot refused: %r" % (stream, answer))

    def snapshot(self, stream: str) -> dict:
        answer = self._send(wire.dumps({"snapshot": stream}).encode("utf-8"))
        if not (isinstance(answer, dict) and answer.get("stream_id") == stream and isinstance(answer.get("k"), int)):
            self._kill("engine answered a snapshot with %r" % (answer,))
            raise EngineFailure(self.failed)
        return answer

    def check(self, stream: str, rows) -> dict:
        """The audit path: replay the rows through the log (`replayRows`, then `check`), and answer the fold of the
        replayed log. Raises `EngineRefusedLog` if they do not replay."""
        answer = self._send(('{"check":{"stream_id":%s,"rows":[%s]}}' % (wire.dumps(stream), _rows_json(rows))).encode("utf-8"),
                            self.startup_timeout)
        if isinstance(answer, dict) and answer.get("checked") == stream:
            return answer
        raise EngineRefusedLog("stream %s: %r" % (stream, answer))

    def drop(self, stream: str) -> None:
        answer = self._send(('{"drop":%s}' % wire.dumps(stream)).encode("utf-8"))
        if answer != {"dropped": stream}:
            self._kill("engine answered a drop with %r" % (answer,))
            raise EngineFailure(self.failed)

    def decide(self, request: dict) -> dict:
        """One request in, one answer out. Any irregularity is fatal."""
        answer = self._send(wire.dumps(request).encode("utf-8"))
        if not _is_answer(answer):
            self._kill("engine answered something that is not an answer: %r" % (answer,))
            raise EngineFailure(self.failed)
        return answer

    def query(self, q: dict) -> object:
        """A read of a stream (`Wire.streamSJ`)."""
        return self._send(wire.dumps(q).encode("utf-8"))

    def line(self, raw: bytes) -> object:
        """One line as it is, and the engine's answer, whatever it is (the stream interface's check, `interface.py`)."""
        return self._send(raw)

    def describe(self) -> dict:
        """The engine's description (`{"query":"describe"}`): `{"revision", "repo", "package", "protocol", "schema":
        {"commands": [...]}}` (schema.py reads it)."""
        answer = self._send(b'{"query":"describe"}')
        if (isinstance(answer, dict) and isinstance(answer.get("revision"), str) and isinstance(answer.get("schema"), dict)
                and isinstance(answer["schema"].get("commands"), list)):
            return answer
        self._kill("engine does not describe itself: %r" % (answer,))
        raise EngineFailure(self.failed)

    def revision(self) -> str:
        """The commit the engine was built from (`{"query":"revision"}`): a commit, `<commit>-dirty`, or `unknown`.
        An engine that does not answer it (built before engines knew their revision) is a failure."""
        return self._revision()["revision"]

    def revision_key(self) -> str:
        """The revision the engine was built from, as a revision key: its commit, and `/<package>` for a package other
        than the repository's root (`revisions.revision_key`)."""
        r = self._revision()
        return r["revision"] + ("/" + r["package"] if r.get("package") else "")

    def _revision(self) -> dict:
        answer = self._send(b'{"query":"revision"}')
        if isinstance(answer, dict) and isinstance(answer.get("revision"), str) and answer["revision"] and \
                isinstance(answer.get("package", ""), str):
            return answer
        self._kill("engine does not report its revision: %r" % (answer,))
        raise EngineFailure(self.failed)

    # -- internals ----------------------------------------------------------------------------------------------------

    def _next(self, timeout: float) -> object:
        try:
            line = self._out.get(timeout=timeout)
        except queue.Empty:
            self._kill("engine did not answer within %ss" % timeout)
            raise EngineFailure(self.failed)
        if line is None:
            code = None
            if self.proc is not None:
                self._reap(self.proc, 5.0)
                code = self.proc.returncode
            self._kill("engine exited (code %s): %s" % (code, self._stderr_text()))
            raise EngineFailure(self.failed)
        try:
            return wire.loads(line)
        except wire.BadJson:
            self._kill("engine wrote a line that is not JSON: %r" % line[:200])
            raise EngineFailure(self.failed)

    @staticmethod
    def _read_out(proc: subprocess.Popen, out: "queue.Queue[Optional[bytes]]") -> None:
        for line in iter(proc.stdout.readline, b""):
            out.put(line)
        out.put(None)

    @staticmethod
    def _read_err(proc: subprocess.Popen, err: List[str]) -> None:
        for line in iter(proc.stderr.readline, b""):
            err.append(line.decode("utf-8", "replace").rstrip())

    def _stderr_text(self) -> str:
        t = getattr(self, "_err_thread", None)
        if t is not None and self.proc is not None and not self._poll(self.proc):
            t.join(timeout=2)
        return " | ".join(self._err)[:2000]

    def _kill(self, why: str) -> None:
        self.failed = why
        p = self.proc
        if p is not None and p.returncode is None:
            try:
                p.kill()
            except OSError:
                pass
            self._reap(p, 0.0)


def _rows_json(rows) -> str:
    """Stored rows `(seq, request JSON, event JSON)` as the engine's `[{"request", "event"}...]`, without the brackets."""
    return ",".join('{"request":%s,"event":%s}' % (req, ev) for _, req, ev in rows)


def _is_answer(a: object) -> bool:
    if not isinstance(a, dict):
        return False
    at = isinstance(a.get("stream_id"), str) and isinstance(a.get("at"), int)
    if a.get("accept") is True:
        return set(a) == {"accept", "event", "stream_id", "at"} and isinstance(a["event"], dict) and at
    if a.get("accept") is False:
        return set(a) == {"accept", "reason", "stream_id", "at"} and isinstance(a["reason"], str) and at
    return set(a) == {"error", "detail"} and a["error"] == "malformed" and isinstance(a["detail"], str)
