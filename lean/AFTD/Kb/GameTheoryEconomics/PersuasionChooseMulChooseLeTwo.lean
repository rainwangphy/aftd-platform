import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionChooseMulChooseLe

/-!
# persuasion_choose_mul_choose_le_two

Topic: mechanism_design   Node: 61ccaf18f5c4

Lemma B. For 2 ≤ u ≤ m and 1 ≤ t ≤ u - 1, C(u,t) C(2m-u, m-t) ≤ 2 C(2m-2, m-1).
-/

open Finset in
/-- **Lemma B.** For `2 ≤ u ≤ m` and `1 ≤ t ≤ u - 1`, `C(u,t) C(2m-u, m-t) ≤ 2 C(2m-2, m-1)`. -/
lemma persuasion_choose_mul_choose_le_two (m u t : ℕ) (hu : 2 ≤ u) (hum : u ≤ m)
    (ht : 1 ≤ t) (htu : t + 1 ≤ u) :
    u.choose t * (2 * m - u).choose (m - t) ≤ 2 * (2 * (m - 1)).choose (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨u', rfl⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hN : 2 * (k + 1) - (u' + 1) = 2 * k + 1 - u' := by omega
  have hmt : k + 1 - (t' + 1) = k - t' := by omega
  have hk : k + 1 - 1 = k := by omega
  rw [hN, hmt, hk, Nat.choose_succ_succ, Nat.add_mul]
  set N := 2 * k + 1 - u' with hNdef
  have h2 : u'.choose t' * N.choose (k - t') ≤ (2 * k).choose k :=
    persuasion_choose_mul_choose_le u' N k t' (by omega) (by omega) (by omega) (by omega)
  have h1 : u'.choose (t' + 1) * N.choose (k - t') ≤ (2 * k).choose k := by
    have s1 : u'.choose (t' + 1) = u'.choose (u' - t' - 1) := by
      rw [show u' - t' - 1 = u' - (t' + 1) by omega, Nat.choose_symm (by omega : t' + 1 ≤ u')]
    have s2 : N.choose (k - t') = N.choose (k - (u' - t' - 1)) := by
      rw [show k - (u' - t' - 1) = N - (k - t') by omega, Nat.choose_symm (by omega : k - t' ≤ N)]
    rw [s1, s2]
    exact persuasion_choose_mul_choose_le u' N k (u' - t' - 1) (by omega) (by omega)
      (by omega) (by omega)
  simp only [Nat.succ_eq_add_one] at *
  omega
