"""Validate the intended DAG and conservative source status; Lean CI checks actual axioms."""
from pathlib import Path
from graphlib import TopologicalSorter
import argparse
import json
import re
from lean_source import project_audit, PROOF_KINDS

ROOT = Path(__file__).resolve().parents[1]
UNFINISHED = {"unproved_statement", "depends_on_unproved",
              "definition_depends_on_unproved", "mathematical_plan"}


def node_status(names, local):
    linked = [local[name] for name in names if name in local]
    if not names:
        return "mathematical_plan"
    if not linked:
        return "formalized_upstream"
    statuses = {record.source_status for record in linked}
    for status in ("unproved_statement", "definition_depends_on_unproved", "depends_on_unproved"):
        if status in statuses:
            return status
    return "proof_candidate" if any(r.kind in PROOF_KINDS for r in linked) else "definition"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    local = project_audit(ROOT)
    sources = []

    def expand(path, stack=()):
        path = path.resolve()
        assert path.is_relative_to((ROOT / "blueprint/src").resolve()), "TeX input leaves source tree"
        assert path not in stack, "Cyclic TeX input"
        sources.append(path.relative_to(ROOT).as_posix())
        text = path.read_text(encoding="utf-8")

        def include(match):
            child = Path(match[1])
            if child.suffix != ".tex":
                child = child.with_suffix(".tex")
            return expand(path.parent / child, stack + (path,))
        return re.sub(r"\\input\{([^}]+)\}", include, text)

    source = expand(ROOT / "blueprint/src/content.tex")
    assert not re.search(r"\\end\{proof\}\s*\\begin\{proof\}", source), (
        "Consecutive proof blocks lose dependency edges")
    pattern = re.compile(
        r"\\begin\{(definition|lemma|theorem|proposition|corollary)\}"
        r"(?:\[([^\]]*)\])?(.*?)\\end\{\1\}"
        r"(?:\s*\\begin\{proof\}(?:\[[^\]]*\])?(.*?)\\end\{proof\})?", re.S)

    def values(command, text):
        return sorted({v.strip() for group in re.findall(r"\\" + command + r"\{([^}]+)\}", text)
                       for v in group.split(",")})

    nodes = []
    marked = {}
    for match in pattern.finditer(source):
        kind, title, body, proof = match.groups()
        labels = values("label", body)
        assert len(labels) == 1, f"Expected one label: {title}"
        names = values("lean", body)
        for name in names:
            if name.startswith(("Preiss.", "PreissBlueprint.")):
                assert name in local, f"Missing exact local declaration: {name}"
                assert not local[name].private, f"Blueprint links a private declaration: {name}"
        status = node_status(names, local)
        nodes.append(dict(
            id=labels[0], title=title, kind=kind, status=status, lean=names,
            verification="pinned_source_audit" if status == "formalized_upstream" else "source_audit_only",
            statement_dependencies=values("uses", body),
            proof_dependencies=values("uses", proof or ""),
            expanded_line=source[:match.start()].count("\n") + 1))
        marked[labels[0]] = "\\leanok" in body + (proof or "")
    ids = [n["id"] for n in nodes]
    assert len(ids) == len(set(ids)), "Duplicate labels"
    graph = {n["id"]: set(n["statement_dependencies"] + n["proof_dependencies"]) for n in nodes}
    for name, deps in graph.items():
        assert name not in deps, f"Self dependency: {name}"
        assert deps <= set(ids), f"Unknown dependencies for {name}: {deps - set(ids)}"
    order = list(TopologicalSorter({k: sorted(v) for k, v in graph.items()}).static_order())
    assert "thm:preiss" in ids
    by_id = {n["id"]: n for n in nodes}
    for label in order:
        node = by_id[label]
        pending = sorted(dep for dep in graph[label] if by_id[dep]["status"] in UNFINISHED)
        if pending and any(name in local for name in node["lean"]):
            if node["status"] == "definition":
                node["status"] = "definition_depends_on_unproved"
            elif node["status"] == "proof_candidate":
                node["status"] = "depends_on_unproved"
        node["unfinished_dependencies"] = pending
        assert not (marked[label] and node["status"] in UNFINISHED), (
            f"Unfinished node is marked leanok: {label}")
    data = dict(
        sources=sources,
        meaning="Intended dependencies and conservative source status, not a certified proof graph",
        status_policy=("A proof candidate has no detected local/source or blueprint obligation; "
                       "only a compiled axiom audit can certify its proof. Definitions may not "
                       "contain placeholders. Theorem proof placeholders are explicit obligations."),
        nodes=nodes, topological_order=order)
    colors = dict(definition="#d9eaf7", unproved_statement="#fff0bf",
                  depends_on_unproved="#ffe0b2", definition_depends_on_unproved="#ffe0b2",
                  proof_candidate="#dce5ee", formalized_upstream="#d9efdb",
                  mathematical_plan="#eeeeee")
    slug = lambda label: label.replace(":", "_").replace("-", "_")
    dot = ["digraph Preiss {", "  rankdir=LR;",
           '  node [shape=box, style=filled, fontname="Arial"];']
    mermaid = ["flowchart LR"]
    for node in nodes:
        label = (node["title"] or node["id"]).replace('"', '\\"')
        dot.append(f'  "{node["id"]}" [label="{label}", fillcolor="{colors[node["status"]]}"];')
        mermaid.append(f'  {slug(node["id"])}["{label}"]')
    for target, deps in graph.items():
        for dep in sorted(deps):
            dot.append(f'  "{dep}" -> "{target}";')
            mermaid.append(f"  {slug(dep)} --> {slug(target)}")
    dot.append("}")
    outputs = {
        "blueprint/dependencies.json": json.dumps(data, indent=2, ensure_ascii=False) + "\n",
        "blueprint/dependencies.dot": "\n".join(dot) + "\n",
        "blueprint/dependencies.mmd": "\n".join(mermaid) + "\n",
    }
    for filename, content in outputs.items():
        path = ROOT / filename
        if args.write:
            path.write_text(content, encoding="utf-8")
        else:
            assert path.read_text(encoding="utf-8") == content, f"Stale export: {filename}"

    # Generate checks for every local named declaration, including nodes not yet linked.
    names = sorted(set(local) | {name for n in nodes for name in n["lean"]})
    imports = {"FormalizingGMT"}
    imports.update(r.path.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
                   for r in local.values())
    if (ROOT / "blueprint/reuse.json").exists():
        inventory = json.loads((ROOT / "blueprint/reuse.json").read_text(encoding="utf-8"))
        imports.update(e["path"].removesuffix(".lean").replace("/", ".")
                       for e in inventory["entries"] if e["project"] == "mathlib")
    checks = [f"import {module}" for module in sorted(imports)]
    checks += [""] + [f"#check {name}" for name in names]
    checks += [""] + [f"#print axioms {name}" for name in names]
    metadata = {
        name: (dict(project="local", kind=local[name].kind,
                    source_status=local[name].source_status,
                    path=local[name].path.relative_to(ROOT).as_posix())
               if name in local else dict(project="upstream", kind="upstream"))
        for name in names
    }
    (ROOT / "tmp").mkdir(exist_ok=True)
    (ROOT / "tmp/blueprint_checks.lean").write_text("\n".join(checks) + "\n", encoding="utf-8")
    (ROOT / "tmp/blueprint_checks.json").write_text(
        json.dumps(metadata, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"Validated {len(nodes)} nodes, {sum(map(len, graph.values()))} edges; DAG is acyclic.")
    print(f"Audited {len(local)} local declarations; theorem obligations remain explicit.")
    print("Run Lean and scripts/check_kernel_axioms.py for actual transitive axiom status.")


if __name__ == "__main__":
    main()
