import AFTD.Prelude

/-!
# young_diagram_max_multiplicity

Topic: combinatorics   Node: 95e1f2ababfe

Provenance: formalization of a published result. Source: arXiv:2610.29291 Theorem 3.4

For a Young diagram $\mu$, its maximum part multiplicity is the maximum count of any row length in $\mu.\text{rowLens}$, computed as $(\mu.\text{rowLens}.\text{map}\; \mu.\text{rowLens}.\text{count}).\text{foldr}\; \max\; 0$.
-/

/-- The maximum multiplicity of any part length in a Young diagram. -/
def young_diagram_max_multiplicity (μ : YoungDiagram) : ℕ := (μ.rowLens.map μ.rowLens.count).foldr max 0
