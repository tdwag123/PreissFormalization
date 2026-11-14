# LeanBlueprint

This is a standard [LeanBlueprint](https://github.com/PatrickMassot/leanblueprint) project.
The canonical mathematical document is `src/content.tex`, which includes the proof
sketch, architecture, upstream inventory, and audited plan. The shared site is
[tdwag123.github.io/PreissFormalization](https://tdwag123.github.io/PreissFormalization/).

Install Graphviz and `pip install -r blueprint/requirements.txt`. From the repository root:

```console
python scripts/test_source_checks.py
python scripts/check_blueprint.py
python scripts/declaration_links.py
python scripts/render_blueprint.py
python scripts/declaration_links.py --site
python scripts/export_core_graph.py --site
python scripts/check_module_plan.py --site
python scripts/check_render.py
leanblueprint serve
```

The wrapper runs the standard LeanBlueprint/plasTeX renderer on temporary TeX
copies. It adds completion markers only from the kernel checkpoint, after
comparing all Lean sources and dependency pins with the audited revision.
The checkout must contain that revision (`git fetch --unshallow` for a shallow clone).
Running `leanblueprint web` directly skips this status synchronization.
The configuration loads the actual LeanBlueprint and dependency-graph plugins.
The generated HTML is `blueprint/web/index.html`. All TeX inputs are adjacent to
`web.tex` so the fallback input resolver also works without a full TeX distribution.

The full interactive graph includes companion results. `preiss-core.svg` contains
only ancestors of the final theorem; `modules.svg` is the proposed import graph.
The corresponding JSON files support independent inspection. The architecture is
proposed; actual source imports may evolve while interfaces are elaborated.

After editing mathematical dependencies or Lean declarations, regenerate the committed data:

```console
python scripts/check_blueprint.py --write
python scripts/declaration_links.py --write
python scripts/export_core_graph.py
dot -Tsvg blueprint/dependencies.dot -o blueprint/dependencies.svg
```

The declaration index links upstream declarations to pinned sources and local
statements to their canonical files. Its viewer displays source syntax, not doc-gen's
elaborated types; implicit parameters and instances remain visible in the source file.
Source-derived status never certifies a proof. The separate Lean workflow elaborates
every local module and inspects `#print axioms` output, including transitive `sorryAx`.
Definitions with placeholder dependencies and new nonstandard axioms fail that audit.
Theorems with explicit obligations are reported as unfinished.

The Pages workflow validates, renders, and publishes the documentation on `main`.
It does not establish that the mathematics is proved. See `validation.json` and the
Lean workflow's kernel-status artifact for their separate scopes.
