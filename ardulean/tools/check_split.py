#!/usr/bin/env python3
"""Check that a split generated file is the original, byte for byte.

    python3 tools/check_split.py [INDEX.json ...]
    python3 tools/check_split.py INDEX.json [--against ORIGINAL.lean] [--write OUT.lean]

(default: ArduLean/Vehicle/INDEX.json and ArduLean/Estimator/INDEX.json, from the repository root). For each index
(written by tools/split_modules.py) every module file is read and must have the split's form exactly:

    import lines | module doc comment | the original header's `open`/`set_option` lines and `namespace NS` line
    | the module's items | at most one blank line | `end NS` (the original's last lines)

Its items are cut from it by the line counts the index records, and all items are put back in the original order. The
original's header (imports and module doc comment), these items and its last lines must give the SHA-256 recorded at
split time; with --against, they must also equal that file; --write writes the rebuilt file (the input of a new
split, tools/split.sh). The umbrella module must import every module of the
index and nothing else of the project. Exit status 1 on any difference.
"""
import hashlib, json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def check(index_path, against=None, write=None):
    idx = json.load(open(index_path))
    src = idx["source"]
    tail, suffix = src["header_tail"], src["suffix"]
    items_of = {}
    for m in idx["modules"]:
        items_of[m["module"]] = [i for i, it in enumerate(idx["items"]) if it["module"] == m["module"]]
    texts = [None] * len(idx["items"])
    for m in idx["modules"]:
        f = ROOT / m["path"]
        t = f.read_text()
        assert t.count(tail) == 1, f"{m['path']}: the original header lines must occur exactly once"
        head, body = t.split(tail)
        lines = head.split("\n")
        k = 0
        while lines[k].startswith("import "): k += 1
        assert lines[k] == "" and lines[k + 1] == "/-!" and head.endswith("-/\n"), f"{m['path']}: header form"
        assert body.endswith(suffix), f"{m['path']}: must end with the original's last lines"
        body = body[:len(body) - len(suffix)]
        bl = body.split("\n")
        pos = 0
        for i in items_of[m["module"]]:
            n = idx["items"][i]["lines"]
            texts[i] = "\n".join(bl[pos:pos + n]) + "\n"
            pos += n
        rest = "\n".join(bl[pos:])
        assert rest in ("", "\n"), f"{m['path']}: text after the last item: {rest[:80]!r}"
    assert all(x is not None for x in texts)
    whole = src["prefix"] + "".join(texts) + suffix
    ok = hashlib.sha256(whole.encode()).hexdigest() == src["sha256"]
    body_ok = hashlib.sha256("".join(texts).encode()).hexdigest() == src["body_sha256"]
    print(f"{index_path}: {len(idx['modules'])} modules, {len(texts)} items, {len(whole.splitlines())} lines; "
          f"body SHA-256 {'OK' if body_ok else 'DIFFERS'}; file SHA-256 {src['sha256'][:16]}… {'OK' if ok else 'DIFFERS'}")
    if write:
        Path(write).write_text(whole)
        print(f"  written to {write}")
    if against:
        same = Path(against).read_text() == whole
        print(f"  against {against}: {'identical' if same else 'DIFFERENT'}")
        ok = ok and same
    umbrella = ROOT / (str(Path(index_path).parent.relative_to(ROOT)) + ".lean")
    imps = [l.split()[1] for l in umbrella.read_text().split("\n") if l.startswith("import ")]
    if sorted(imps) != sorted(m["module"] for m in idx["modules"]):
        print(f"  {umbrella.relative_to(ROOT)}: does not import exactly the modules of the index"); ok = False
    return ok and body_ok


def main():
    args = sys.argv[1:]
    against = write = None
    if "--against" in args:
        i = args.index("--against"); against = args[i + 1]; del args[i:i + 2]
    if "--write" in args:
        i = args.index("--write"); write = args[i + 1]; del args[i:i + 2]
    paths = [Path(a).resolve() for a in args] or [ROOT / "ArduLean/Vehicle/INDEX.json", ROOT / "ArduLean/Estimator/INDEX.json"]
    assert not ((against or write) and len(paths) > 1), "--against and --write take one index"
    ok = all([check(p, against, write) for p in paths])
    print("OK" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
