import AFTD.Prelude
import AFTD.Kb.Tcs.OneLayeredFamily

/-!
# one_layered_max_layers

Topic: combinatorics   Node: b227868cc893

Provenance: formalization of a published result. Source: arXiv:2611.08071 Section 2

For natural numbers m and r, one_layered_max_layers m r is the supremum (maximum) over all n ≤ m and all 1-layered families of r-subsets on Fin n of the number of layers k, which is 0 if no such family exists (in particular when m < r).
-/

/-- The maximum number of layers F(m, r) in a 1-layered family of r-subsets using at most m vertices, defined as 0 when m < r. -/
noncomputable def one_layered_max_layers (m r : ℕ) : ℕ := sSup {k : ℕ | ∃ n ≤ m, ∃ (F : OneLayeredFamily (Fin n) r), F.k = k}
