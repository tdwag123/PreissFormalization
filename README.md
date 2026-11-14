# PreissFormalization

A reusable LeanBlueprint for Preiss' rectifiability theorem, following De Lellis, Theorem 6.1.
This is the initial **definitions and proof-plan stage**, not a completed formalization.

Open the [shared LeanBlueprint](https://tdwag123.github.io/PreissFormalization/) or its
[interactive dependency graph](https://tdwag123.github.io/PreissFormalization/dep_graph_document.html).
The graph has **89 nodes and 261 edges**, including **43 existing FormalizingGMT nodes**
covering **62 upstream declarations**, with links to pinned source locations.

Start with [the blueprint](blueprint/src/content.tex), its [build instructions](blueprint/README.md),
and the [dependency graph](blueprint/dependencies.svg). The rendered LeanBlueprint is generated at
`blueprint/web/index.html`. [The dependency data](blueprint/dependencies.json) is generated from the
same LaTeX source, with separate statement and intended proof edges.

The main route is:

1. Reuse FormalizingGMT's density and tangent APIs, especially `mattila_14_9` (all tangents uniform).
2. Obtain a flat tangent almost everywhere (De Lellis 6.8).
3. Prove uniqueness at infinity, the conical flatness gap, and rigidity from flatness at infinity.
4. Use the first-crossing argument to make every tangent flat (6.10).
5. Apply the Marstrand–Mattila rectifiability criterion (5.1).

`Preiss/` contains reusable definitions and elementary proved bridges, with no `sorry` or axioms.
`PreissBlueprint/` is a separate statement laboratory with explicit `sorry` obligations. Its final
theorem assembles the intended argument but still depends on those obligations. Compiling it checks
interfaces, not proofs. Technical nodes without Lean links remain mathematical specifications.

```lean
theorem preiss (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x) :
    IsRectifiableMeasure m μ
```

Here `m n : ℕ`, `Euclidean n = EuclideanSpace ℝ (Fin n)`, and the density predicate uses
FormalizingGMT's closed-ball ratio `μ (closedBall x r) / (2*r)^m`. The blueprint explicitly includes
the open-ball normalization bridge, dimension zero, and `m > n`.

Rectifiable measures require both absolute continuity with respect to mathlib's Hausdorff measure
and concentration on countably many Lipschitz images. The graph/image equivalence and density
representation on a sigma-finite carrier are separate obligations. The general metric-target
definition uses globally defined Euclidean parametrizations; equivalence with arbitrary-domain
parametrizations is intended here for Euclidean targets, not asserted for every metric target.

The existing `IsTangentMeasure`, `IsSUniform`, and `Measure.WeaklyConverges` are imported.
Fixed-dimensional tangents are separate: arbitrary-scalar tangents are positive multiples of them,
not literally the same set. Quantitative flatness statements use unit-mass uniform measures.

Dependencies: FormalizingGMT `c14a8d07b2df61798fc184fd53ff6f72d858ae48`,
mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean `v4.34.1`.
See [the reuse inventory](blueprint/reuse.json) and [validation record](blueprint/validation.json).

```console
lake update
lake build Preiss
lake build PreissBlueprint
python scripts/check_blueprint.py
lake env lean tmp/blueprint_checks.lean
```

The default build includes only `Preiss`. No proved theorem should import the draft library.
