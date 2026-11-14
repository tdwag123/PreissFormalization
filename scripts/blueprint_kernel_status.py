"""Bind blueprint completion colours to a kernel audit of the same Lean sources."""
from pathlib import Path
import io
import json
import re
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
INPUTS = {"lean-toolchain", "lake-manifest.json", "lakefile.toml"}


def is_proof_input(path):
    return path in INPUTS or (
        path.endswith(".lean") and (
            path.startswith(("Preiss/", "PreissBlueprint/"))
            or path in {"Preiss.lean", "PreissBlueprint.lean"}
        )
    )


def same_sources(recorded, current):
    normalize = lambda data: data.replace(b"\r\n", b"\n")
    return recorded.keys() == current.keys() and all(
        normalize(data) == normalize(current[name]) for name, data in recorded.items()
    )


def sources_match_checkpoint(root, revision):
    assert re.fullmatch(r"[0-9a-f]{40}", revision), "Invalid checkpoint revision"
    archive = subprocess.check_output(
        ["git", "-c", f"safe.directory={root.as_posix()}", "archive", revision], cwd=root
    )
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        recorded = {m.name: tar.extractfile(m).read() for m in tar.getmembers()
                    if m.isfile() and is_proof_input(m.name)}
    paths = [root / p for p in INPUTS | {"Preiss.lean", "PreissBlueprint.lean"}]
    for directory in ("Preiss", "PreissBlueprint"):
        paths.extend((root / directory).rglob("*.lean"))
    current = {p.relative_to(root).as_posix(): p.read_bytes() for p in paths if p.is_file()}
    return same_sources(recorded, current)


def node_status(names, records, source_matches):
    linked = [records.get(name) for name in names]
    statements = bool(names) and source_matches and all(row is not None for row in linked)
    proved = statements and all(set(row["axioms"]) <= STANDARD for row in linked)
    return {"statement_checked": statements, "proof_checked": bool(proved)}


def load_status(root=ROOT):
    checkpoint = json.loads((root / "blueprint/kernel-checkpoint.json").read_text(encoding="utf8"))
    assert not checkpoint["failures"], "Cannot colour nodes from a failed kernel audit"
    revision = checkpoint["source_revision"]
    matched = sources_match_checkpoint(root, revision)
    graph = json.loads((root / "blueprint/dependencies.json").read_text(encoding="utf8"))
    return {
        "source_revision": revision,
        "sources_match_checkpoint": matched,
        "nodes": {n["id"]: node_status(n["lean"], checkpoint["declarations"], matched)
                  for n in graph["nodes"]},
    }
