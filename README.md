# PreissFormalization

A reusable Lean library and LeanBlueprint for Preiss's rectifiability theorem,
following De Lellis's *Lecture Notes on Rectifiable Sets, Densities, and Tangent Measures*.
**`Preiss.preiss` is proved. Its transitive axiom dependencies are only**
**`propext`, `Classical.choice`, and `Quot.sound`; it does not depend on `sorryAx`.**

The [statement and dependency audit](blueprint/src/statement-audit.tex) verifies
the closed-ball, Lipschitz-image formulation. Formal bridges to the paper's
open-ball density and Lipschitz-graph conventions remain unfinished; the claim
of completion does not include those translations or the tangent converse.
The compiled traversal reaches 62,920 declarations with no unavailable bodies
and no unfinished dependencies. The corrected 444-node core graph covers all
621 named local declarations reached by that traversal.

- [Read the shared LeanBlueprint](https://tdwag123.github.io/PreissFormalization/).
- [Explore the complete dependency graph](https://tdwag123.github.io/PreissFormalization/dep_graph_document.html).
- [View the dependencies of Preiss alone](https://tdwag123.github.io/PreissFormalization/preiss-core.svg).
- [Inspect the proposed module graph](https://tdwag123.github.io/PreissFormalization/modules.svg).

The blueprint begins with a [natural-language proof sketch](blueprint/src/proof-sketch.tex),
then explains the [library organization](blueprint/src/architecture.tex) and gives the
[intermediate mathematical obligations](blueprint/src/plan.tex).
[Existing FormalizingGMT results](blueprint/src/upstream.tex) appear as dependency nodes,
with exact names and links to pinned source. [The reuse inventory](blueprint/reuse.json)
also identifies mathlib tools. The [validation record](blueprint/validation.json)
distinguishes source checks, statement compilation, and completed proofs.

The [verified proof checkpoint](https://github.com/tdwag123/PreissFormalization/actions/runs/43649878386)
at `f84dbbb` built every local module and audited 781 declarations. Its
[kernel report](blueprint/kernel-checkpoint.json) verifies `Preiss.preiss` with only the
three permitted foundations. 14 companion declarations still depend on `sorryAx`;
none is a dependency of the main theorem.

The proof policy permits only Lean/mathlib's standard foundations: `propext`,
`Classical.choice`, and `Quot.sound`. CI rejects nonstandard axioms, unfinished
definitions, new declarations that depend on `sorryAx`, and regressions of previously
certified proofs. Existing open obligations remain explicitly tracked until proved.

The proof route is:

1. Reuse FormalizingGMT to show that almost every tangent is uniform.
2. Use recentering and dimension reduction to find a flat tangent almost everywhere.
3. Prove uniform-measure blow-down uniqueness, a conical flatness gap, and rigidity
   when the blow-down is flat.
4. Use a greatest-crossing argument to show that every tangent is flat.
5. Apply the Marstrand–Mattila sufficient criterion for rectifiability.

The plan includes Lipschitz graphs, partial-domain Lipschitz parametrizations,
rectifiable sets and measures, and the full tangent-measure characterization.
Its converse, graph decomposition, and graph area formula form an unfinished companion
branch outside the main Preiss proof. The following characterization statements are
included in the blueprint but are not yet completely formalized: under positive finite lower and upper density bounds,
rectifiability is equivalent to every tangent being flat almost everywhere.
Rectifiability further yields one common tangent plane and an existing density there.

```lean
theorem Preiss.preiss (μ : Measure (Preiss.Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, Preiss.HasPositiveFiniteDensityAt m μ x) :
    Preiss.IsRectifiableMeasure m μ
```

Here `m n : ℕ`; the zero and excessive dimensions are included. Density uses
FormalizingGMT's closed-ball, diameter-normalized convention. Fixed-dimensional
blow-ups have a separate definition: arbitrary-scalar tangents form a positive ray,
while a rectifiable measure has a single limit under fixed-dimensional normalization.

Canonical statements and proofs live in their topic files under `Preiss/`.
Remaining companion obligations retain explicit `sorry` bodies; definitions contain no placeholders. `PreissBlueprint/` is now a compatibility import of the canonical library. A source link means that a
statement is written, not that it has compiled or been proved. The full intended DAG
is not an extraction of completed Lean proof terms.

Dependencies are pinned to FormalizingGMT `c14a8d07b2df61798fc184fd53ff6f72d858ae48`,
mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, and Lean `v4.34.1`.
Preserve `lake-manifest.json` when reproducing the build.

```console
python scripts/check_blueprint.py
python scripts/check_module_plan.py
python scripts/declaration_links.py
```

The Lean CI workflow builds **every local module**, including modules absent from
an umbrella import, then records actual transitive axiom dependencies. To build the
same target list in PowerShell:

```powershell
$preissTargets = (python scripts/lean_targets.py) -split ' '
lake build @preissTargets
lake env lean tmp/blueprint_checks.lean | Tee-Object tmp/blueprint-kernel.log
python scripts/check_kernel_axioms.py tmp/blueprint-kernel.log
```

See [blueprint build instructions](blueprint/README.md) for the rendered documentation.

Independent proof candidates in `checks/*.lean` run on separate GitHub Actions
runners, with up to eight concurrent jobs. They import the pinned canonical
modules and audit every named candidate declaration against the same three
standard foundations. These checks supplement the full project build; candidate
files are not imported into the library or counted as completed blueprint nodes.
This permits additional compilation without exhausting local memory.
