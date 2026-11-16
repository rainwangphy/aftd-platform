import AFTD.Prelude
import AFTD.Kb.Tcs.RecSeqU

/-!
# sign_chamber_vector

Topic: combinatorics   Node: 6b7a60786a93

Provenance: formalization of a published result. Source: arXiv:2611.17360 line 120

For any natural number n, sign_chamber_vector n is the vector in Fin n → ℝ whose coordinate at i : Fin n is (rec_seq_u n - rec_seq_u (n - (i.val + 1)) : ℝ).
-/

/-- The canonical vector in Fin n → ℝ with i-th coordinate equal to u(n) - u(n - (i + 1)). -/
noncomputable def sign_chamber_vector (n : ℕ) : Fin n → ℝ := fun i => (rec_seq_u n - rec_seq_u (n - (i.val + 1)) : ℝ)
