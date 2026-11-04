import AFTD.Prelude

/-!
# gaussian_majority_error

Topic: communication   Node: 35c329dc9e48

Provenance: formalization of a published result. Source: arXiv:2610.16830, The Communication Complexity of the Coin Problem; OP-994

The real-valued function gaussian_majority_error (q : ℕ) (lam : ℝ) : ℝ is defined as the infimum in ℝ over all f : ℝ → Fin q with Measurable f and all g : Fin q → ℝ → Bool satisfying ∀ m : Fin q, Measurable (g m) of ((ProbabilityTheory.gaussianReal 0 ⟨lam ^ 2, sq_nonneg lam⟩).prod (ProbabilityTheory.gaussianReal 0 1) {p : ℝ × ℝ | (g (f p.1) p.2 = true) ≠ (0 < p.1 + p.2)}).toReal.
-/

/-- The infimum of error probability in estimating sign(X+Y) over all measurable one-way encoders with q messages and decoders, where X ~ N(0, lam^2) and Y ~ N(0, 1) are independent. -/
noncomputable def gaussian_majority_error (q : ℕ) (lam : ℝ) : ℝ := ⨅ (f : ℝ → Fin q) (_ : Measurable f) (g : Fin q → ℝ → Bool) (_ : ∀ m, Measurable (g m)),
    ((ProbabilityTheory.gaussianReal 0 ⟨lam ^ 2, sq_nonneg lam⟩).prod (ProbabilityTheory.gaussianReal 0 1)
      {p : ℝ × ℝ | (g (f p.1) p.2 = true) ≠ (0 < p.1 + p.2)}).toReal
