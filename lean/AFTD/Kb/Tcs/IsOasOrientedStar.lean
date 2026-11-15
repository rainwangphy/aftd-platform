import AFTD.Prelude
import AFTD.Kb.Tcs.OrientedStarDensity
import AFTD.Kb.Tcs.DigraphonSymmetrization
import AFTD.Kb.Tcs.IsDigraphon

/-!
# is_oas_oriented_star

Topic: combinatorics   Node: c2987299cc0e

Provenance: formalization of a published result. Source: arXiv:2611.15027 Definition 1

An oriented star with center c is oriented anti-Sidorenko (OAS) if for every digraphon W, its density in W is at most its density in (W + W^T) / 2.
-/

/-- An oriented star is oriented anti-Sidorenko (OAS) if its density in any digraphon is at most its density in the symmetrized digraphon. -/
def is_oas_oriented_star {V : Type*} [Fintype V]
    (D : Digraph V) [DecidableRel D.Adj] (c : V) : Prop := ∀ W : ℝ → ℝ → ℝ, is_digraphon W →
    oriented_star_density D c W ≤ oriented_star_density D c (digraphon_symmetrization W)
