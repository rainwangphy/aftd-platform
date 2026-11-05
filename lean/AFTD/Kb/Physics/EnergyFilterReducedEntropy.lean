import AFTD.Prelude

/-!
# energy_filter_reduced_entropy

Topic: statistical_mechanics   Node: 87047ef1ebaa

Provenance: formalization of a published result. Source: arXiv:2405.02158

For a sequence a : ℤ → ℝ and dimensions n, m : ℕ, letting l = n - m and M sA sB = a ((n : ℤ) / 2 - |sA| - |sB|) for bitstrings sA : Fin m → Bool and sB : Fin l → Bool, energy_filter_reduced_entropy a n m is 0 if the trace of M M^T is 0, and otherwise the entropy ∑ s, Real.negMulLog (λ_s / tr) of the normalized eigenvalues λ_s of M M^T.
-/

/-- Von Neumann entropy of the reduced state of the energy-filtered state on m qubits, via the spectrum of M M^T. -/
noncomputable def energy_filter_reduced_entropy (a : ℤ → ℝ) (n m : ℕ) : ℝ :=
  let l := n - m
  let wA : (Fin m → Bool) → ℤ := fun s => ∑ j : Fin m, if s j then 1 else 0
  let wB : (Fin l → Bool) → ℤ := fun s => ∑ j : Fin l, if s j then 1 else 0
  let M : Matrix (Fin m → Bool) (Fin l → Bool) ℝ :=
    fun sA sB => a ((n : ℤ) / 2 - wA sA - wB sB)
  let hR := Matrix.isHermitian_mul_conjTranspose_self M
  let tr := ∑ s, hR.eigenvalues s
  if tr = 0 then 0 else ∑ s, Real.negMulLog (hR.eigenvalues s / tr)
