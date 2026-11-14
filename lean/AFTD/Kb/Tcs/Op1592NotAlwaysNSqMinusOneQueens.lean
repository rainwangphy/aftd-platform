import AFTD.Prelude
import AFTD.Kb.Tcs.IsNonAttackingQueens
import AFTD.Kb.Tcs.ModularQueensAttack

/-!
# op_1592_not_always_n_sq_minus_one_queens

Topic: combinatorics   Node: baafe28576eb

Provenance: formalization of a published result. Source: arXiv:2611.14754 Sec. 4

It is not the case that for every integer n ≥ 2 all of whose prime factors are at most 7, one can place n^2 - 1 mutually non-attacking queens in (Z/nZ)^3.
-/

lemma op_1592_not_always_n_sq_minus_one_queens_zmod2_attack {d : ℕ} (x y : Fin d → ZMod 2) (h : x ≠ y) :
    modular_queens_attack x y := by
  use 1
  let v : Fin d → SignType := fun i => if x i - y i = 1 then SignType.pos else SignType.zero
  use v
  refine ⟨by decide, ?_, ?_⟩
  · intro hv
    apply h
    ext i
    have hvi : v i = 0 := congr_fun hv i
    dsimp [v] at hvi
    by_cases hxy : x i - y i = 1
    · rw [if_pos hxy] at hvi
      exact False.elim (by revert hvi; decide)
    · rw [if_neg hxy] at hvi
      have hz0 : x i - y i = 0 := by
        generalize hz : x i - y i = z at *
        fin_cases z
        · rfl
        · contradiction
      exact sub_eq_zero.mp hz0
  · intro i
    dsimp [v]
    by_cases hxy : x i - y i = 1
    · rw [if_pos hxy]
      simp [SignType.cast, hxy]
    · rw [if_neg hxy]
      have hz0 : x i - y i = 0 := by
        generalize hz : x i - y i = z at *
        fin_cases z
        · rfl
        · contradiction
      simp [SignType.cast, hz0]

/-- Refutation of the sub-question in OP-1592: it is false that n^2 - 1 non-attacking queens can always be placed on (Z/nZ)^3 when prime factors of n are at most 7. -/
theorem op_1592_not_always_n_sq_minus_one_queens :
    ¬ (∀ n : ℕ, 2 ≤ n → (∀ p : ℕ, p.Prime → p ∣ n → p ≤ 7) →
      ∃ s : Finset (Fin 3 → ZMod n), is_non_attacking_queens s ∧ s.card = n^2 - 1) := by
  intro H
  have h2 : 2 ≤ 2 := le_rfl
  have hprime : ∀ p : ℕ, p.Prime → p ∣ 2 → p ≤ 7 := by
    intro p _ hp2
    have : p ≤ 2 := Nat.le_of_dvd (by decide) hp2
    omega
  obtain ⟨s, hs, hcard⟩ := H 2 h2 hprime
  have hle : s.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro a b ha hb
    by_contra h
    exact hs ha hb h (op_1592_not_always_n_sq_minus_one_queens_zmod2_attack a b h)
  omega
