#!/usr/bin/env python3
"""Content-hash every source CHC file so 2025's verdicts can be carried back.

CHC-COMP re-formats and renames benchmarks every year, so the only reliable
join between the 2018-2024 sets and the 2025 set (the only one that ships
expected verdicts) is the file content itself.  Where a hash matches, the
verdict is the same fact about the same clause system and can be reused; where
it does not, the task stays `unknown`.
"""
import csv, gzip, hashlib, pathlib, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paths import WORK as SP  # noqa: E402


def digest(path):
    opener = gzip.open if str(path).endswith(".gz") else open
    h = hashlib.sha1()
    try:
        with opener(path, "rb") as fh:
            for chunk in iter(lambda: fh.read(1 << 16), b""):
                h.update(chunk)
    except Exception:
        return None
    return h.hexdigest()


rows = []
for f in (SP / "jobs.tsv", SP / "jobs25.tsv"):
    for line in f.read_text().splitlines():
        p = line.split("\t")
        rows.append(p + [""] * (6 - len(p)))

# 2025 rows carry the verdict; build hash -> verdict from them first.
by_hash = {}
out = []
for task, src, year, track, orig, verdict in rows:
    d = digest(src)
    out.append((task, src, year, track, orig, verdict, d or ""))
    if verdict in ("true", "false") and d:
        by_hash.setdefault(d, verdict)

recovered = 0
with open(SP / "sources.csv", "w", newline="") as fh:
    w = csv.writer(fh)
    w.writerow(["task", "year", "track", "orig_name", "verdict", "verdict_src", "sha1"])
    for task, src, year, track, orig, verdict, d in out:
        if verdict in ("true", "false"):
            vsrc = "chc-comp25-yml"
        elif d and d in by_hash:
            verdict, vsrc = by_hash[d], "chc-comp25-yml-by-content"
            recovered += 1
        else:
            verdict, vsrc = "unknown", ""
        w.writerow([task, year, track, orig, verdict, vsrc, d])

print("rows: %d   verdicts recovered by content hash: %d" % (len(out), recovered))
