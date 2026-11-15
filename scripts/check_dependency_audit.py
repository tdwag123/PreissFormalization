"""Compare a compiled-term dependency walk with the curated blueprint."""
from pathlib import Path
import json
import os

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def main():
    read = lambda path: json.loads((ROOT / path).read_text(encoding="utf8"))
    audit = read("tmp/preiss-kernel-dependencies.json")
    checkpoint = read("blueprint/kernel-checkpoint.json")
    graph = read("blueprint/dependencies.json")
    core = read("blueprint/preiss-core.json")
    records = {row["name"]: row for row in audit["declarations"]}
    assert audit["root"] == "Preiss.preiss"
    assert set(audit["cached_axioms"]) <= STANDARD, audit["cached_axioms"]
    assert set(audit["raw_axioms"]) <= STANDARD, audit["raw_axioms"]
    assert "sorryAx" not in records
    unfinished = {n for n, r in checkpoint["declarations"].items() if "sorryAx" in r["axioms"]}
    assert not unfinished.intersection(records), "An unfinished declaration is reachable"
    linked = {n for node in graph["nodes"] for n in node["lean"]}
    core_names = {n for node in core["nodes"] for n in node["lean"]}
    local = {name for name, row in records.items() if row["module"].startswith("Preiss.")}
    named_local = local.intersection(checkpoint["declarations"])
    boundaries = [r for r in audit["declarations"] if r["module"].startswith("FormalizingGMT.")]
    result = {
        "source_revision": os.environ.get("GITHUB_SHA"),
        "root": audit["root"],
        "total_reachable_declarations": len(records),
        "reachable_local_declarations_in_checkpoint": sorted(named_local),
        "reachable_local_declarations_outside_blueprint_core": sorted(named_local - core_names),
        "reachable_local_declarations_not_linked": sorted(named_local - linked),
        "reachable_formalizingGMT_declarations": sorted(r["name"] for r in boundaries),
        "unavailable_constants": audit["missing_constants"],
        "cached_axioms": audit["cached_axioms"],
        "raw_axioms": audit["raw_axioms"],
        "unfinished_reachable": sorted(unfinished.intersection(records)),
        "scope": "Compiled constant types and available values; this does not replace semantic review of definitions or inspect tactic execution.",
    }
    (ROOT / "tmp/preiss-dependency-comparison.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf8")
    print(json.dumps({k: v for k, v in result.items() if not k.startswith("reachable_")}, indent=2))
    print(f"Named local dependencies: {len(named_local)}; outside intended core: {len(named_local-core_names)}")
    print(f"FormalizingGMT dependencies: {len(boundaries)}")


if __name__ == "__main__":
    main()
