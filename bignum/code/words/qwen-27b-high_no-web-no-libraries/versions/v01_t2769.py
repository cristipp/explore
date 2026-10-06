obj = None
try:
    obj = parse(line)
    idval = obj["id"]
    s = int(obj["a"]) + int(obj["b"])
    ans = to_words(s)
    out_line = '{"id": ' + dumps(idval) + ', "answer": ' + dumps(ans) + '}\n'
except Exception:
    try:
        idval = obj["id"] if obj is not None else None
    except Exception:
        idval = None
    try:
        out_line = '{"id": ' + dumps(idval) + ', "answer": null}\n'
    except Exception:
        out_line = '{"id": null, "answer": null}\n'
write(out_line)
flush()
