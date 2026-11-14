"""Export the dependency closure of Preiss independently of companion theorems."""
from pathlib import Path
import argparse
import json
import subprocess
from blueprint_kernel_status import load_status

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--site", action="store_true")
    args = parser.parse_args()
    data = json.loads((ROOT / "blueprint/dependencies.json").read_text(encoding="utf8"))
    nodes = {n["id"]: n for n in data["nodes"]}
    closure = set()

    def visit(key):
        if key in closure:
            return
        closure.add(key)
        for dep in nodes[key]["statement_dependencies"] + nodes[key]["proof_dependencies"]:
            visit(dep)

    visit("thm:preiss")
    selected = [n for n in data["nodes"] if n["id"] in closure]
    kernel = load_status()
    core = {"root": "thm:preiss", "meaning": data["meaning"], "nodes": selected,
            "kernel_checkpoint": kernel["source_revision"],
            "sources_match_checkpoint": kernel["sources_match_checkpoint"]}
    destination = ROOT / "blueprint"
    (destination / "preiss-core.json").write_text(json.dumps(core, indent=2) + "\n", encoding="utf8")
    lines = ['digraph PreissCore {', 'rankdir=LR;',
             'node [shape=box, style=filled, fontname="Arial"];']
    for n in selected:
        verified = kernel["nodes"][n["id"]]["proof_checked"]
        attrs = {"label": n["title"] or n["id"],
                 "fillcolor": "#1CAC78" if verified else "#fff0bf",
                 "tooltip": n["id"] + ": " + (
                     "kernel verified at " + kernel["source_revision"][:7]
                     if verified else "unfinished or not verified at this source revision")}
        lines.append(json.dumps(n["id"]) + " [" + ", ".join(
            k + "=" + json.dumps(v) for k, v in attrs.items()) + "];")
        for dep in sorted(set(n["statement_dependencies"] + n["proof_dependencies"])):
            lines.append(json.dumps(dep) + " -> " + json.dumps(n["id"]) + ";")
    lines.append("}")
    dot = destination / "preiss-core.dot"
    dot.write_text("\n".join(lines) + "\n", encoding="utf8")
    if args.site:
        web = destination / "web"
        web.mkdir(exist_ok=True)
        subprocess.run(["dot", "-Tsvg", str(dot), "-o", str(web / "preiss-core.svg")], check=True)
        (web / "preiss-core.json").write_text(json.dumps(core, indent=2) + "\n", encoding="utf8")
    print(f"Preiss closure: {len(selected)} of {len(nodes)} nodes")


if __name__ == "__main__":
    main()
