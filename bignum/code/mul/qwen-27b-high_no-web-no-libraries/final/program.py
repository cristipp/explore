import sys
import json
import time

ONES = (
    "zero", "one", "two", "three", "four", "five", "six", "seven",
    "eight", "nine", "ten", "eleven", "twelve", "thirteen", "fourteen",
    "fifteen", "sixteen", "seventeen", "eighteen", "nineteen"
)

TENS = (
    "", "", "twenty", "thirty", "forty", "fifty",
    "sixty", "seventy", "eighty", "ninety"
)

TWO = tuple(
    ONES[i] if i < 20 else (
        TENS[i // 10] if i % 10 == 0 else TENS[i // 10] + "-" + ONES[i % 10]
    )
    for i in range(100)
)

GROUP = tuple(
    TWO[i] if i < 100 else (
        ONES[i // 100] + " hundred" + (" " + TWO[i % 100] if i % 100 else "")
    )
    for i in range(1000)
)

SCALES = (
    "", "thousand", "million", "billion", "trillion",
    "quadrillion", "quintillion", "sextillion", "septillion",
    "octillion", "nonillion", "decillion"
)


def number_to_words(n, GROUP=GROUP, SCALES=SCALES, scale_len=len(SCALES)):
    if n == 0:
        return "zero"
    if n < 0:
        return "negative " + number_to_words(-n)

    parts = []
    i = 0
    while n:
        n, g = divmod(n, 1000)
        if g:
            s = GROUP[g]
            if i < scale_len and i:
                s += " " + SCALES[i]
            parts.append(s)
        i += 1

    parts.reverse()
    return " ".join(parts)


def to_int(x):
    if isinstance(x, int):
        return x
    if isinstance(x, float):
        return int(x)
    s = str(x).strip().replace(",", "")
    try:
        return int(s)
    except Exception:
        return int(float(s))


def main():
    limit = 30.0
    argv = sys.argv

    for k in range(1, len(argv)):
        arg = argv[k]
        if arg == "--time-limit":
            if k + 1 < len(argv):
                try:
                    limit = float(argv[k + 1])
                except Exception:
                    pass
            break
        if arg.startswith("--time-limit="):
            try:
                limit = float(arg.split("=", 1)[1])
            except Exception:
                pass
            break

    deadline = time.monotonic() + limit

    loads = json.loads
    dumps = json.dumps
    words = number_to_words
    to_int_local = to_int

    items = []
    for line in sys.stdin.buffer.read().splitlines():
        if not line:
            continue
        try:
            obj = loads(line)
            items.append((obj.get("id"), obj.get("a"), obj.get("b")))
        except Exception:
            pass

    write = sys.stdout.write
    flush = sys.stdout.flush
    now = time.monotonic
    total = len(items)

    for idx in range(total):
        if now() >= deadline:
            for j in range(idx, total):
                write('{"id": ' + dumps(items[j][0]) + ', "answer": null, "timeout": true}\n')
                flush()
            break

        i, a, b = items[idx]
        try:
            ans = words(to_int_local(a) * to_int_local(b))
        except Exception:
            write('{"id": ' + dumps(i) + ', "answer": null, "timeout": true}\n')
            flush()
            continue

        if now() >= deadline:
            write('{"id": ' + dumps(i) + ', "answer": null, "timeout": true}\n')
            flush()
            for j in range(idx + 1, total):
                write('{"id": ' + dumps(items[j][0]) + ', "answer": null, "timeout": true}\n')
                flush()
            break

        write('{"id": ' + dumps(i) + ', "answer": ' + dumps(ans) + '}\n')
        flush()

    sys.exit(0)


if __name__ == "__main__":
    try:
        main()
    except SystemExit:
        raise
    except Exception:
        sys.exit(0)
