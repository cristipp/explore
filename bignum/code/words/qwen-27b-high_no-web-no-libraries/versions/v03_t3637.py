import sys
import json
import time

ONES = (
    "zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
    "ten", "eleven", "twelve", "thirteen", "fourteen", "fifteen", "sixteen",
    "seventeen", "eighteen", "nineteen",
)
TENS = (
    "", "", "twenty", "thirty", "forty", "fifty",
    "sixty", "seventy", "eighty", "ninety",
)

def u100(n):
    if n == 0:
        return ""
    if n < 20:
        return ONES[n]
    tens, ones = divmod(n, 10)
    if ones:
        return TENS[tens] + "-" + ONES[ones]
    return TENS[tens]

def u1000(n):
    if n < 100:
        return u100(n)
    hundreds, rest = divmod(n, 100)
    s = ONES[hundreds] + " hundred"
    if rest:
        s += " " + u100(rest)
    return s

SMALL = tuple(u1000(i) for i in range(1000))
SCALES = (
    "", "thousand", "million", "billion", "trillion",
    "quadrillion", "quintillion", "sextillion", "septillion",
    "octillion", "nonillion", "decillion",
)
SCALES_LEN = len(SCALES)

def words(n, SMALL=SMALL, SCALES=SCALES, SCALES_LEN=SCALES_LEN):
    if n == 0:
        return "zero"
    if n < 0:
        return "negative " + words(-n)
    parts = []
    i = 0
    while n:
        n, g = divmod(n, 1000)
        if g:
            s = SMALL[g]
            if i and i < SCALES_LEN:
                s += " " + SCALES[i]
            parts.append(s)
        i += 1
    return " ".join(reversed(parts))

def parse(line, loads=json.loads):
    try:
        return loads(line)
    except TypeError:
        return loads(line.decode("utf-8-sig"))

def get_limit():
    args = sys.argv
    for i, arg in enumerate(args):
        if arg == "--time-limit" and i + 1 < len(args):
            try:
                return float(args[i + 1])
            except Exception:
                return 30.0
        if arg.startswith("--time-limit="):
            try:
                return float(arg.split("=", 1)[1])
            except Exception:
                return 30.0
    return 30.0

def main():
    limit = get_limit()
    start = time.monotonic()
    deadline = start + limit
    lines = sys.stdin.buffer.read().splitlines()
    out = sys.stdout
    write = out.write
    flush = out.flush
    p = parse
    dumps = json.dumps
    now = time.monotonic
    total = len(lines)

    for idx in range(total):
        line = lines[idx]
        if not line.strip():
            continue
        if now() >= deadline:
            for rest in lines[idx:]:
                if not rest.strip():
                    continue
                obj = None
                try:
                    obj = p(rest)
                    idv = obj.get("id") if isinstance(obj, dict) else None
                except Exception:
                    idv = None
                try:
                    payload = dumps({"id": idv, "answer": None, "timeout": True})
                except Exception:
                    payload = '{"id": null, "answer": null, "timeout": true}'
                write(payload + "\n")
                flush()
            return

        obj = None
        try:
            obj = p(line)
            idv = obj["id"]
            s = int(obj["a"]) + int(obj["b"])
            ans = words(s)
            payload = dumps({"id": idv, "answer": ans})
        except Exception:
            idv = obj.get("id") if isinstance(obj, dict) else None
            try:
                payload = dumps({"id": idv, "answer": None})
            except Exception:
                payload = '{"id": null, "answer": null}'
        write(payload + "\n")
        flush()

if __name__ == "__main__":
    try:
        main()
    except Exception:
        pass
    sys.exit(0)
