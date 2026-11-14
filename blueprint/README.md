This is a standard [LeanBlueprint](https://github.com/PatrickMassot/leanblueprint) project.
The canonical mathematical sources are [src/content.tex](src/content.tex) and
[src/upstream.tex](src/upstream.tex). The shared site is
https://tdwag123.github.io/PreissFormalization/.

Install Graphviz and `pip install -r blueprint/requirements.txt`. From the repository root,
LeanBlueprint's CLI can build and serve the site once the project is in a Git repository:

```console
leanblueprint web
python scripts/declaration_links.py --site
python scripts/check_render.py
leanblueprint serve
```

The equivalent renderer invocation also works without Git: run `plastex -c plastex.cfg web.tex`
from `blueprint/src`. This loads the actual LeanBlueprint and dependency-graph plugins.
The generated site is `blueprint/web/index.html`; its dependency graph links to individual statements.
GitHub Actions validates and renders every pull request, and publishes `main` to GitHub Pages.
Lean links open a portable declaration viewer with pinned upstream source links and explicit
status labels. It shows source syntax, not elaborated doc-gen types; surrounding implicit
parameters and instances must be read in the linked source.

`src/print.tex` also supports a print build when a LaTeX toolchain is available.
The HTML build is the primary output for this initial blueprint.

The lightweight graph exports use the same source:

```console
python scripts/check_blueprint.py --write
python scripts/check_blueprint.py
python scripts/declaration_links.py --write
dot -Tsvg blueprint/dependencies.dot -o blueprint/dependencies.svg
lake build Preiss PreissBlueprint
lake env lean tmp/blueprint_checks.lean
```

`dependencies.json` distinguishes statement and intended proof dependencies. In the standalone
graph, green means formalized upstream (source audited), blue means a local definition, amber means a draft
Lean statement, and gray means a mathematical plan without a finalized Lean declaration.
These colors do not certify proofs. `PreissBlueprint.preiss` depends on `sorryAx`.

The 43 existing GMT nodes use `\leanok` markers for declarations and proof bodies present in
upstream source. New planned theorems have no such markers. This source audit does not claim a
complete fresh kernel build of upstream or successful elaboration of the downstream draft library.
The first-crossing argument and technical moment identities still need more detailed Lean
interfaces; their requirements and source sections are recorded.

The graph contains 89 nodes and 261 edges. Its 62 GMT declarations include density bounds,
Hausdorff density estimates, finite-restriction regularity, Vitali covering, vague compactness,
tangent existence/matching, good sets, Mattila 14.7 and 14.9, radial integral equality, and uniform
measure dimension reduction. New adapters preserve the blow-up witnesses absent from existing
existential dimension-reduction statements. Edges show selected mathematical dependencies and
proposed downstream uses, not an exhaustive extraction of Lean proof terms.

`declarations.json` is a committed source index for all 101 linked declarations. Regenerate it
with `python scripts/declaration_links.py --write` after `lake update` if upstream revisions or
Lean declarations change. Site builds validate this index without downloading the Lean toolchain.
See `validation.json` for the incomplete Lean-build status; the Pages workflow checks documentation,
not Lean proofs.
