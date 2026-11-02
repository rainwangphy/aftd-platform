import AFTD.Prelude

/-!
# ising_polynomial_real_simple_root_location

Topic: statistical_mechanics   Node: 06bcc7dabe2c

Provenance: helper lemma. arXiv:2610.39815, Sections 2–4; helper for OP-806.

A nonzero real polynomial has only real simple complex roots, all at most 1, with at most one nonpositive root.
-/

noncomputable def ising_polynomial_real_simple_root_location (P : Polynomial ℝ) : Prop := P ≠ 0 ∧
  (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).IsRoot z →
    z.im = 0 ∧ z.re ≤ 1 ∧ (P.map (algebraMap ℝ ℂ)).derivative.eval z ≠ 0) ∧
  (∀ z w : ℂ, (P.map (algebraMap ℝ ℂ)).IsRoot z →
    (P.map (algebraMap ℝ ℂ)).IsRoot w → z.re ≤ 0 → w.re ≤ 0 → z = w)
