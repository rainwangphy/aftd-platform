import AFTD.Prelude

/-!
# recurrence_profile

Topic: combinatorics   Node: cc568a0ae281

Provenance: formalization of a published result. Source: arXiv:2611.01561 Sec. 2

For N : ℕ, b, c : Fin (N + 1) → ℝ, and i : Fin (N + 1), the profile is b i + c i.
-/

/-- Profile sequence d_i = b_i + c_i on Fin (N + 1). -/
noncomputable def recurrence_profile (N : ℕ) (b c : Fin (N + 1) → ℝ) (i : Fin (N + 1)) : ℝ := b i + c i
