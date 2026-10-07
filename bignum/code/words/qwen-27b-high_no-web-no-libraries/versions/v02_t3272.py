import sys, json, time

ONES = ("zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten", "eleven", "twelve", "thirteen", "fourteen", "fifteen", "sixteen", "seventeen", "eighteen", "nineteen")
TENS = ("", "", "twenty", "thirty", "forty", "fifty", "sixty", "seventy", "eighty", "ninety")

def u100(n):
    if n == 0:
        return ""
    if n < 20:
        return ONES[n]
    r = n % 10
    if r:
        return TENS[n // 10] + "-" + ONES[r]
    return TENS[n // 10]

def u1000(n):
    if n < 100:
        return u100(n)
    h = n // 100
    r = n % 100
    s = ONES[h] + " hundred"
    if r:
        s += " " + u100(r)
    return s

SMALL = tuple(u1000(i) for i in range(1000))
SCALES = ("", "thousand", "million", "billion", "trillion", "quadrillion", "quintillion", "sextillion", "septillion", "octillion", "nonillion", "decillion")

def words(n):
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
            if i and i < len(SCALES):
                s += " " + SCALES[i]
            parts.append(s)
        i += 1
    return " ".join(reversed(parts))

def get_limit():
    for i, a in enumerate(sys.argv):
        if a == "--time-limit" and i + 1 < len(sys.argv):
            try:
                return float(sys.argv[i + 1])
            except ValueError:
                return 30.0
        if a.startswith("--time-limit="):
            try:
                return float(a.split("=", 1)[1])
            except ValueError:
                return 30.0
    return 30.0

def main():
    limit = get_limit()
    deadline = time.monotonic() + limit
    lines = sys.stdin.buffer.read().splitlines()
    out = sys.stdout
    loads = json.loads
    dumps = json.dumps
    for idx, line in enumerate(lines):
        if not line:
            continue
        if time.monotonic() >= deadline:
            for rest in lines[idx:]:
                if not rest:
                    continue
                try:
                    obj = loads(rest)
                    idv = obj.get("id") if isinstance(obj, dict) else None
                except Exception:
                    idv = None
                out.write(dumps({"id": idv, "answer": None, "timeout": True}) + "\n")
                out.flush()
            return
        try:
            obj = loads(line)
            idv = obj["id"]
            ans = words(int(obj["a"]) + int(obj["b"]))
            out.write(dumps({"id": idv, "answer": ans}) + "\n")
        except Exception:
            idv = None
            try:
                idv = obj["id"]
            except Exception:
                pass
            out.write(dumps({"id": idv, "answer": None}) + "\n")
        out.flush()

if __name__ == "__main__":
    try:
        main()
    except Exception:
        pass
    sys.exit(0)
