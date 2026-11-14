"""Read Lean's actual #print axioms output; never infer proof certification from source."""
from pathlib import Path
import argparse
import json
import os
import re

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
PROOFS = {"theorem", "lemma"}


def parse_axioms(text):
    result = {}
    pattern = r"'([^\r\n]+?)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, text, re.S):
        result[match[1]] = sorted({s.strip() for s in (match[2] or "").split(",") if s.strip()})
    return result


def check(metadata, axioms, baseline=None):
    assert set(metadata) <= set(axioms), f"Missing kernel reports: {set(metadata) - set(axioms)}"
    records = {}
    failures = []
    for name, item in metadata.items():
        used = set(axioms[name])
        local = item["project"] == "local"
        is_proof = item["kind"] in PROOFS
        allowed = STANDARD | ({"sorryAx"} if is_proof else set())
        unexpected = used - allowed
        if local and unexpected:
            failures.append(f"{name}: unexpected axioms {sorted(unexpected)}")
        if local and baseline is not None and "sorryAx" in used:
            previous = baseline.get(name)
            if previous is None:
                failures.append(f"{name}: new declaration depends on sorryAx")
            elif "sorryAx" not in previous["axioms"]:
                failures.append(f"{name}: previously certified declaration now depends on sorryAx")
        if "sorryAx" in used:
            status = ("unproved_statement" if item.get("source_status") == "unproved_statement"
                      else "depends_on_sorry")
        else:
            status = "proved" if is_proof else "definition_checked" if local else "upstream_checked"
        records[name] = {**item, "axioms": sorted(used), "kernel_status": status}
    return records, failures


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("log")
    parser.add_argument("--output", default="tmp/kernel-status.json")
    args = parser.parse_args()
    raw = Path(args.log).read_bytes()
    text = raw.decode("utf-16" if raw.startswith((b"\xff\xfe", b"\xfe\xff")) else "utf-8")
    metadata = json.loads((ROOT / "tmp/blueprint_checks.json").read_text(encoding="utf-8"))
    checkpoint = ROOT / "blueprint/kernel-checkpoint.json"
    baseline = json.loads(checkpoint.read_text(encoding="utf-8"))["declarations"]
    records, failures = check(metadata, parse_axioms(text), baseline=baseline)
    report = dict(
        toolchain=(ROOT / "lean-toolchain").read_text().strip(),
        source_revision=os.environ.get("GITHUB_SHA"),
        meaning="Kernel axiom dependencies of the compiled declarations, not just textual references",
        declarations=records, failures=failures)
    output = ROOT / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    assert not failures, "\n".join(failures)
    pending = sum("sorryAx" in r["axioms"] for r in records.values())
    print(f"Checked {len(records)} compiled axiom reports; {pending} declarations still depend on sorryAx.")
    print(f"Kernel report: {output}")


if __name__ == "__main__":
    main()
