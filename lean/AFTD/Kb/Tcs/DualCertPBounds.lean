import AFTD.Prelude
import AFTD.Kb.Tcs.TriangularNumber
import AFTD.Kb.Tcs.DualCertP

/-!
# dual_cert_p_bounds

Topic: combinatorics   Node: 7318d3300816

Provenance: helper lemma. step towards dual_certificate_identity

For any positive integer m, dual_cert_p m is between 1 and m, and when it is at least 2, every triangular number T_k for k < dual_cert_p m - 1 satisfies T_k + dual_cert_p m < m.
-/

namespace DCB1

theorem tri_mono {a b : ℕ} (h : a ≤ b) : triangular_number a ≤ triangular_number b := by
  unfold triangular_number
  exact Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

end DCB1

/-- Bounds on dual_cert_p m: dual_cert_p m is between 1 and m, and when it is at least 2, every triangular number T_k for k < dual_cert_p m - 1 satisfies T_k + dual_cert_p m < m. -/
theorem dual_cert_p_bounds (m : ℕ) (hm : 1 ≤ m) :
    1 ≤ dual_cert_p m ∧ dual_cert_p m ≤ m ∧
      (2 ≤ dual_cert_p m → ∀ k < dual_cert_p m - 1, triangular_number k + dual_cert_p m < m) := by
  unfold dual_cert_p
  dsimp only
  split_ifs with h
  · have hmem := Finset.max'_mem _ h
    generalize Finset.max' _ h = M at hmem ⊢
    simp only [Finset.mem_filter, Finset.mem_Icc] at hmem
    refine ⟨by omega, by omega, fun _ k hk => ?_⟩
    have := DCB1.tri_mono (show k ≤ M - 2 by omega)
    omega
  · exact ⟨le_rfl, hm, fun h2 => absurd h2 (by omega)⟩
