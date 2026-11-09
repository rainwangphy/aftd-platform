import AFTD.Prelude

/-!
# ocycap_fractional_cost

Topic: online_algorithms   Node: 7a9a12d10a6b

Provenance: formalization of a published result. Source: arXiv:2611.08570 Section 2.2

The fractional cost of a weight vector x on pairs of vertices of a cycle on n vertices is the sum of weights x(e) over all candidate links e in the complete graph on Fin n.
-/

/-- The total fractional cost of a link weight vector x on the candidate links. -/
noncomputable def ocycap_fractional_cost (n : ℕ) (x : Sym2 (Fin n) → ℝ) : ℝ := ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, x e
