"""Export the dependency closure of Preiss independently of companion theorems."""
from pathlib import Path
import argparse
import json
import subprocess

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
    core = {"root": "thm:preiss", "meaning": data["meaning"], "nodes": selected}
    destination = ROOT / "blueprint"
    (destination / "preiss-core.json").write_text(json.dumps(core, indent=2) + "\n", encoding="utf8")
    colors = {"formalized_upstream": "#d9efdb", "definition": "#d9eaf7",
              "draft_statement": "#fff0bf", "mathematical_plan": "#eeeeee"}
    lines = ['digraph PreissCore {', 'rankdir=LR;',
             'node [shape=box, style=filled, fontname="Arial"];']
    for n in selected:
        attrs = {"label": n["title"] or n["id"],
                 "fillcolor": colors.get(n["status"], "#fff0bf"),
                 "tooltip": n["id"] + ": " + n["status"]}
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
