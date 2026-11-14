"""Build pinned source links with explicit, non-certified source status.

Run --write after changing names, sources, or upstream revisions; --site installs
the portable viewer after LeanBlueprint rendering. Normal checks need no checkout.
"""
from pathlib import Path
import argparse
import json
import shutil
from lean_source import declarations_in, project_audit

ROOT = Path(__file__).resolve().parents[1]
REPOS = {
    "PreissFormalization": "https://github.com/tdwag123/PreissFormalization",
    "FormalizingGMT": "https://github.com/uw-math-ai/FormalizingGMT",
    "mathlib": "https://github.com/leanprover-community/mathlib4",
}
UNFINISHED = {"unproved_statement", "depends_on_unproved", "definition_depends_on_unproved"}


def declarations(directory):
    """Compatibility iterator for consumers of the original source-index helper."""
    for record in declarations_in(directory):
        if not record.anonymous:
            yield record.name, record.path, record.line, record.signature


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--site", action="store_true")
    args = parser.parse_args()
    graph = json.loads((ROOT / "blueprint/dependencies.json").read_text(encoding="utf-8"))
    names = {name for node in graph["nodes"] for name in node["lean"]}
    graph_status = {}
    for node in graph["nodes"]:
        for name in node["lean"]:
            if node["status"] in UNFINISHED:
                graph_status[name] = node["status"]
    local = project_audit(ROOT)
    registry_path = ROOT / "blueprint/declarations.json"
    inventory = json.loads((ROOT / "blueprint/reuse.json").read_text(encoding="utf-8"))
    revisions = inventory["revisions"]
    if args.write:
        entries = {}
        upstream = ROOT / ".lake/packages/FormalizingGMT"
        mathlib = ROOT / ".lake/packages/mathlib"
        locations = [
            (ROOT, ROOT / "Preiss", "PreissFormalization", "main"),
            (ROOT, ROOT / "PreissBlueprint", "PreissFormalization", "main"),
            (upstream, upstream / "FormalizingGMT", "FormalizingGMT", revisions["FormalizingGMT"]),
        ]
        for path in sorted({e["path"] for e in inventory["entries"] if e["project"] == "mathlib"}):
            locations.append((mathlib, mathlib / path, "mathlib", revisions["mathlib"]))
        for base, folder, project, revision in locations:
            for record in declarations_in(folder):
                name = record.name
                if name not in names:
                    continue
                assert name not in entries, f"Ambiguous declaration: {name}"
                relative = record.path.relative_to(base).as_posix()
                if project == "PreissFormalization":
                    assert name in local
                    source_status = graph_status.get(name, local[name].source_status)
                    pending = sorted(local[name].unfinished_dependencies)
                else:
                    source_status, pending = "formalized_upstream", []
                entries[name] = dict(
                    project=project, revision=revision, path=relative, line=record.line,
                    url=f"{REPOS[project]}/blob/{revision}/{relative}#L{record.line}",
                    signature=record.signature, kind=record.kind,
                    source_status=source_status, unfinished_dependencies=pending,
                    verification="Source index only; consult the Lean CI kernel-status artifact.")
        assert names == entries.keys(), f"Names not resolved: {names - entries.keys()}"
        registry_path.write_text(json.dumps(entries, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    entries = json.loads(registry_path.read_text(encoding="utf-8"))
    assert names == entries.keys(), "Declaration index is stale"
    for name, entry in entries.items():
        if entry["project"] in revisions:
            assert entry["revision"] == revisions[entry["project"]], f"Stale upstream revision: {name}"
        else:
            assert name in local, f"Missing exact declaration: {name}"
            record = local[name]
            assert entry["path"] == record.path.relative_to(ROOT).as_posix(), f"Stale source path: {name}"
            assert entry["line"] == record.line, f"Stale source line: {name}"
            assert entry["signature"] == record.signature, f"Stale source signature: {name}"
            expected = graph_status.get(name, record.source_status)
            assert entry.get("source_status") == expected, f"Stale source status: {name}"
    if args.site:
        target = ROOT / "blueprint/web/lean/find"
        target.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / "blueprint/source-viewer.html", target / "index.html")
        shutil.copyfile(registry_path, target / "declarations.json")
        (ROOT / "blueprint/web/.nojekyll").touch()
    count = sum(e["project"] == "FormalizingGMT" for e in entries.values())
    print(f"Validated source locations for {len(entries)} declarations ({count} from FormalizingGMT).")
    print("Local theorem status includes detected unfinished source/blueprint dependencies; kernel CI is separate.")


if __name__ == "__main__":
    main()
