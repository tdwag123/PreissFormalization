"""Validate the proposed import DAG and render the module overview."""
from pathlib import Path
from graphlib import TopologicalSorter
import argparse
import json
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--site", action="store_true")
    args = parser.parse_args()
    path = ROOT / "blueprint/modules.json"
    data = json.loads(path.read_text(encoding="utf8"))
    modules = {m["module"]: m for m in data["modules"]}
    assert len(modules) == len(data["modules"]), "Duplicate modules"
    graph = {k: set(v["local_imports"]) for k, v in modules.items()}
    for k, deps in graph.items():
        assert k not in deps, f"Self import: {k}"
        assert deps <= modules.keys(), f"Missing modules for {k}: {deps - modules.keys()}"
    order = list(TopologicalSorter(graph).static_order())
    assert set(order) == set(data["topological_order"])
    lines = ['digraph Modules {', 'rankdir=LR;',
             'node [shape=box, style=filled, fontname="Arial"];']
    for key, m in modules.items():
        label = key.removeprefix("Preiss.")
        color = "#e4eaf5" if m.get("scope") == "companion" else "#eeeeee"
        lines.append(json.dumps(key) + " [label=" + json.dumps(label) +
                     ", fillcolor=" + json.dumps(color) + "];")
        for dep in sorted(graph[key]):
            lines.append(json.dumps(dep) + " -> " + json.dumps(key) + ";")
    lines.append("}")
    dot = ROOT / "blueprint/modules.dot"
    dot.write_text("\n".join(lines) + "\n", encoding="utf8")
    if args.site:
        web = ROOT / "blueprint/web"
        web.mkdir(exist_ok=True)
        subprocess.run(["dot", "-Tsvg", str(dot), "-o", str(web / "modules.svg")], check=True)
        (web / "modules.json").write_text(path.read_text(encoding="utf8"), encoding="utf8")
    print(f"Proposed module graph: {len(modules)} modules, acyclic")


if __name__ == "__main__":
    main()
