import AFTD.Prelude

/-!
# subadditive_gen_variance

Topic: information   Node: ba2ba4fc3f12

Provenance: helper lemma. arXiv:2610.21231 (On the subadditivity of mutual f-information), Appendix B, proof of Lemma 4

The generalized variance functional L_{u,p}(q) = E_p[g(q/p) (u - E_q u)²] of eq. (22) of arXiv:2610.21231.
-/

/-- The generalized variance functional L_{u,p}(q) = E_p[gw(q/p) (u - E_q u)^2]. -/
noncomputable def subadditive_gen_variance {X : Type*} [Fintype X] (gw : ℝ → ℝ) (pX u q : X → ℝ) : ℝ :=
  ∑ x, pX x * gw (q x / pX x) * (u x - ∑ x', q x' * u x') ^ 2
