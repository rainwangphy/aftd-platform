import AFTD.Prelude

/-!
# rademacher_expect

Topic: statistical_mechanics   Node: 03f947653b47

Provenance: original. Related work: knowledgebase: OP-1152

For a natural number m and a real random variable X on Fin m → Bool, rademacher_expect m X is the uniform expectation 2^(-m) * sum_{s} X(s).
-/

/-- The uniform expectation of a real random variable on the finite space of Rademacher signs Fin m → Bool. -/
noncomputable def rademacher_expect (m : ℕ) (X : (Fin m → Bool) → ℝ) : ℝ := (∑ s : Fin m → Bool, X s) / (2 ^ m : ℝ)
