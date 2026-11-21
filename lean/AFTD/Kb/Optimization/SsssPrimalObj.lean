import AFTD.Prelude

/-!
# ssss_primal_obj

Topic: lp_duality   Node: b6b818badb3f

Provenance: formalization of a published result. Source: arXiv:2611.26188, Section 3

For a finite vertex type V with decidable equality, a set of directed edges E : Finset (V × V), and edge cost and flow functions c, x : V × V → ℝ, the primal objective value ssss_primal_obj E c x is the sum over all edges e ∈ E of c(e) * x(e).
-/

/-- Objective value of a primal solution x to (SSSS-P) with edge costs c. -/
def ssss_primal_obj {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (c : V × V → ℝ) (x : V × V → ℝ) : ℝ := ∑ e ∈ E, c e * x e
