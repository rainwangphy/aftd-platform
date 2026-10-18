import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetIsMidpointBalanced
import AFTD.Kb.Tcs.MidpointCertificateMatrixMinorAbsLe
import AFTD.Kb.Tcs.MidpointCertificateMatrixMinorDvdP
import AFTD.Kb.Tcs.FinsetMidpointBalancedExistsNonzeroMinor

/-!
# finset_card_ge_one_add_clog_of_midpoint_balanced

Topic: combinatorics   Node: e9d74bf161ee

Provenance: formalization of a published result. Source: arXiv:2610.09349 (A near-quadratic lower bound for sets with no unique sums), Lemma B.1 (second statement), proved there by a determinant argument on the midpoint-certificate matrix (rows 2e_i − e_{u_i} − e_{v_i}) with the unit-incidence minor lemma (Lemma 2.2).

For a prime p, every nonempty balanced subset B of Z/pZ has |B| ≥ 1 + ⌈log₂ p⌉.
-/

theorem finset_card_ge_one_add_clog_of_midpoint_balanced {p : ℕ} [Fact p.Prime]
    (B : Finset (ZMod p)) (hB : finset_is_midpoint_balanced B) : 1 + Nat.clog 2 p ≤ B.card := by
  obtain ⟨k, hk0, hk, u, v, b, hinj, hmid, i₀, j₀, hdet_ne⟩ :=
    finset_midpoint_balanced_exists_nonzero_minor B hB
  let M := (Matrix.of fun (i j : Fin (k + 1)) =>
    (if j = i then (2 : ℤ) else 0) - (if j = u i then 1 else 0) - (if j = v i then 1 else 0)).submatrix
    i₀.succAbove j₀.succAbove
  let D := M.det
  have hD_ne : D ≠ 0 := hdet_ne
  have hle : |D| ≤ (2 ^ k : ℤ) := midpoint_certificate_matrix_minor_abs_le u v i₀ j₀
  have hdvd : (p : ℤ) ∣ D := midpoint_certificate_matrix_minor_dvd_p hk0 u v b hinj hmid i₀ j₀
  have hpos : 0 < D.natAbs := Int.natAbs_pos.mpr hD_ne
  have hdvd' : p ∣ D.natAbs := Int.ofNat_dvd_left.mp hdvd
  have hp_le_D : p ≤ D.natAbs := Nat.le_of_dvd hpos hdvd'
  have hD_le_pow : D.natAbs ≤ 2 ^ k := by
    have : (D.natAbs : ℤ) ≤ ((2 ^ k : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      push_cast
      exact hle
    exact Nat.cast_le.mp this
  have hp_le_pow : p ≤ 2 ^ k := hp_le_D.trans hD_le_pow
  have hclog : Nat.clog 2 p ≤ k := (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr hp_le_pow
  omega
