import sys
import os
import json
import time
import select
import re

try:
    import fcntl
except ImportError:
    fcntl = None


def parse_time_limit(argv):
    limit = 30.0
    i = 0
    n = len(argv)
    while i < n:
        arg = argv[i]
        if arg == "--time-limit":
            if i + 1 < n:
                try:
                    limit = float(argv[i + 1])
                except Exception:
                    pass
            i += 2
        elif arg.startswith("--time-limit="):
            try:
                limit = float(arg.split("=", 1)[1])
            except Exception:
                pass
            i += 1
        else:
            i += 1

    if limit != limit or limit < 0.0:
        limit = 30.0
    if limit > 3600.0:
        limit = 3600.0
    return limit


ONES = (
    "zero", "one", "two", "three", "four", "five",
    "six", "seven", "eight", "nine",
)
TEENS = (
    "ten", "eleven", "twelve", "thirteen", "fourteen",
    "fifteen", "sixteen", "seventeen", "eighteen", "nineteen",
)
TENS = (
    "", "", "twenty", "thirty", "forty",
    "fifty", "sixty", "seventy", "eighty", "ninety",
)
SCALES = (
    "", "thousand", "million", "billion", "trillion",
    "quadrillion", "quintillion", "sextillion", "septillion",
)


def chunk_word(n):
    if n == 0:
        return ""
    h, r = divmod(n, 100)
    if h:
        s = ONES[h] + " hundred"
        if r == 0:
            return s
        if r < 10:
            return s + " " + ONES[r]
        if r < 20:
            return s + " " + TEENS[r - 10]
        t, u = divmod(r, 10)
        return s + " " + TENS[t] + ("-" + ONES[u] if u else "")

    if r < 10:
        return ONES[r]
    if r < 20:
        return TEENS[r - 10]
    t, u = divmod(r, 10)
    return TENS[t] + ("-" + ONES[u] if u else "")


WORDS = [chunk_word(i) for i in range(1000)]


def number_words(n):
    if n == 0:
        return "zero"
    if n < 0:
        return "-" + number_words(-n)

    parts = []
    i = 0
    while n:
        n, c = divmod(n, 1000)
        if c:
            w = WORDS[c]
            if i:
                w += (" " + SCALES[i]) if i < len(SCALES) else (" scale" + str(i))
            parts.append(w)
        i += 1
    return " ".join(reversed(parts))


MISSING = object()
ID_RE = re.compile(rb'"id"\s*:\s*("[^"]*"|[^,}\s]+)')


def emit(obj):
    sys.stdout.write(json.dumps(obj, separators=(",", ":")) + "\n")
    sys.stdout.flush()


def emit_answer(idv, ans):
    emit({"id": idv, "answer": ans})


def emit_timeout(idv):
    emit({"id": idv, "answer": None, "timeout": True})


def get_id(line):
    try:
        obj = json.loads(line)
        if isinstance(obj, dict):
            return obj.get("id", MISSING)
    except Exception:
        m = ID_RE.search(line)
        if m:
            tok = m.group(1)
            try:
                return json.loads(tok)
            except Exception:
                return tok.decode("utf-8", "ignore")
    return MISSING


def process_line(line, deadline):
    if not line.strip():
        return False

    try:
        obj = json.loads(line)
    except Exception:
        if time.monotonic() >= deadline:
            idv = get_id(line)
            if idv is not MISSING:
                emit_timeout(idv)
                return True
        return False

    if not isinstance(obj, dict):
        return False

    idv = obj.get("id", MISSING)
    if time.monotonic() >= deadline:
        emit_timeout(None if idv is MISSING else idv)
        return True

    try:
        ans = number_words(int(obj.get("a")) * int(obj.get("b")))
    except Exception:
        ans = None

    if time.monotonic() >= deadline:
        emit_timeout(None if idv is MISSING else idv)
        return True

    emit_answer(None if idv is MISSING else idv, ans)
    return False


def flush_timeouts(buf):
    for line in bytes(buf).splitlines():
        if line.strip():
            idv = get_id(line)
            if idv is not MISSING:
                emit_timeout(idv)


def read_available(buf):
    while True:
        try:
            r, _, _ = select.select([0], [], [], 0.0)
        except Exception:
            break
        if not r:
            break
        try:
            chunk = os.read(0, 65536)
        except Exception:
            break
        if not chunk:
            break
        buf.extend(chunk)


def main():
    limit = parse_time_limit(sys.argv[1:])
    deadline = time.monotonic() + limit
    fd = 0

    old_flags = None
    if fcntl is not None:
        try:
            old_flags = fcntl.fcntl(fd, fcntl.F_GETFL)
            fcntl.fcntl(fd, fcntl.F_SETFL, old_flags | os.O_NONBLOCK)
        except Exception:
            old_flags = None

    buf = bytearray()
    timed_out = False

    while True:
        rem = deadline - time.monotonic()
        if rem < 0.0:
            rem = 0.0

        try:
            r, _, _ = select.select([fd], [], [], rem)
        except Exception:
            try:
                chunk = os.read(fd, 65536)
            except Exception:
                chunk = b""
            if not chunk:
                break
        else:
            if not r:
                timed_out = True
                break
            try:
                chunk = os.read(fd, 65536)
            except BlockingIOError:
                continue
            except Exception:
                timed_out = True
                break
            if not chunk:
                break

        buf.extend(chunk)

        while True:
            nl = buf.find(b"\n")
            if nl < 0:
                break
            line = bytes(buf[:nl])
            del buf[:nl + 1]
            if process_line(line, deadline):
                timed_out = True
                break

        if timed_out:
            break

    if timed_out:
        read_available(buf)
        flush_timeouts(buf)
    else:
        if buf.strip():
            if time.monotonic() >= deadline:
                flush_timeouts(buf)
            else:
                process_line(bytes(buf), deadline)

    if old_flags is not None:
        try:
            fcntl.fcntl(fd, fcntl.F_SETFL, old_flags)
        except Exception:
            pass


if __name__ == "__main__":
    try:
        main()
    except Exception:
        pass
    sys.exit(0)
