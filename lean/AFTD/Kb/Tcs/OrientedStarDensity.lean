import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphInDegree
import AFTD.Kb.Tcs.DigraphonInMarginal
import AFTD.Kb.Tcs.DigraphonOutMarginal
import AFTD.Kb.Tcs.DigraphOutDegree

/-!
# oriented_star_density

Topic: combinatorics   Node: e2f3dd92ad73

Provenance: formalization of a published result. Source: arXiv:2611.15027 Section 6.1

The homomorphism density of an oriented star with center c in a digraphon W is the integral over x in [0, 1] of (W^-(x))^(inDegree c) * (W^+(x))^(outDegree c).
-/

/-- Homomorphism density of an oriented star with center c in a digraphon W. -/
noncomputable def oriented_star_density {V : Type*} [Fintype V]
    (D : Digraph V) [DecidableRel D.Adj] (c : V) (W : ℝ → ℝ → ℝ) : ℝ := ∫ x in Set.Icc (0 : ℝ) 1,
    (digraphon_in_marginal W x) ^ (digraph_in_degree D c) *
    (digraphon_out_marginal W x) ^ (digraph_out_degree D c)
