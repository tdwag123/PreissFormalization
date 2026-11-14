"""Run independent proof candidates against actual pinned imports on a CI runner.

This does not certify the project or replace its full kernel audit. Every named
candidate declaration must compile and use only the standard foundations.
"""
from pathlib import Path
import argparse
import json
import re
import subprocess

from check_kernel_axioms import STANDARD, parse_axioms
from lean_source import mask_noncode, parse_source, PLACEHOLDER

ROOT = Path(__file__).resolve().parents[1]


def candidate(path, root=ROOT):
    path = Path(path)
    if not re.fullmatch(r"checks/[A-Za-z0-9_]+\.lean", path.as_posix()):
        raise ValueError("Expected checks/Name.lean")
    source = (root / path).read_text(encoding="utf-8")
    records = list(parse_source(source, path))
    if not records:
        raise ValueError("No candidate declarations")
    if PLACEHOLDER.search(mask_noncode(source)) or any(r.kind == "axiom" for r in records):
        raise ValueError("Candidate contains an axiom or unfinished proof")
    if any(r.private or r.anonymous for r in records):
        raise ValueError("Candidates must use named public declarations for the axiom audit")
    modules = sorted(set(re.findall(r"^(?:public )?import ([\w.]+)\s*$", source, re.M)))
    if not modules or any(not m.startswith(("Preiss.", "FormalizingGMT.", "Mathlib.")) for m in modules):
        raise ValueError("Candidates must import canonical project or pinned dependency modules")
    return source, [r.name for r in records], modules


def audit(names, log):
    reports = parse_axioms(log)
    missing = set(names) - reports.keys()
    if missing:
        raise ValueError(f"Missing kernel reports: {sorted(missing)}")
    for name in names:
        unexpected = set(reports[name]) - STANDARD
        if unexpected:
            raise ValueError(f"{name}: forbidden axioms {sorted(unexpected)}")
    return {name: reports[name] for name in names}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("path", nargs="?")
    parser.add_argument("--matrix", action="store_true")
    parser.add_argument("--targets", action="store_true")
    args = parser.parse_args()
    if args.matrix:
        paths = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / "checks").glob("*.lean"))
        for path in paths:
            candidate(path)
        print("matrix=" + json.dumps({"check": paths}))
        return
    source, names, modules = candidate(args.path)
    if args.targets:
        print("modules=" + " ".join(modules))
        return
    folder = ROOT / "tmp" / "remote-proof-checks"
    folder.mkdir(parents=True, exist_ok=True)
    stem = Path(args.path).stem
    generated = folder / (stem + ".lean")
    generated.write_text(source + "\n" + "\n".join("#print axioms " + n for n in names) + "\n", encoding="utf-8")
    log = folder / (stem + ".log")
    with log.open("w", encoding="utf-8") as output:
        process = subprocess.Popen(["lake", "env", "lean", str(generated.relative_to(ROOT))],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, encoding="utf-8")
        for line in process.stdout:
            print(line, end="", flush=True)
            output.write(line)
        status = process.wait()
    if status:
        raise SystemExit(status)
    reports = audit(names, log.read_text(encoding="utf-8"))
    (folder / (stem + ".json")).write_text(json.dumps(reports, indent=2) + "\n", encoding="utf-8")
    print(f"Checked {len(reports)} candidate declarations with standard foundations only.")


if __name__ == "__main__":
    main()
