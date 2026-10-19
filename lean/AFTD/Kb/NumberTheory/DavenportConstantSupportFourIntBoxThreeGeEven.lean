import AFTD.Prelude
import AFTD.Kb.NumberTheory.DavenportConstantSupport
import AFTD.Kb.NumberTheory.IntBoxThree
import AFTD.Kb.NumberTheory.DavenportBoxThreeEvenSequence
import AFTD.Kb.NumberTheory.DavenportBoxThreeEvenSequenceMinimal
import AFTD.Kb.NumberTheory.DavenportBoxThreeEvenSequenceCard
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.NumberTheory.MultisetIsMinimalZeroSum
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# davenport_constant_support_four_int_box_three_ge_even

Topic: elementary_number_theory   Node: eb9bbc553239

Provenance: formalization of a published result. Source: arXiv:2610.16562 Theorem 3 (even case).

Theorem 3 of arXiv:2610.16562, even m: for every even m ≥ 2, the maximal length of a minimal zero-sum sequence over [[-m,m]]^3 with support of size 4 is at least 16m^3 - 16m^2 + 8m - 1.
-/

theorem davenport_constant_support_four_int_box_three_ge_even (m : ℕ) (hm : 2 ≤ m) (heven : Even m) :
    ((16 * m ^ 3 - 16 * m ^ 2 + 8 * m - 1 : ℕ) : ℕ∞) ≤
      davenport_constant_support 4 (int_box_three m) := by
  let s := davenport_box_three_even_sequence m
  have hmem : ((16 * m ^ 3 - 16 * m ^ 2 + 8 * m - 1 : ℕ) : ℕ∞) ∈
      {n | ∃ s : Multiset (Fin 3 → ℤ), (∀ x ∈ s, x ∈ int_box_three m) ∧ multiset_is_minimal_zero_sum s ∧
        s.toFinset.card = 4 ∧ (Multiset.card s : ℕ∞) = n} := by
    refine ⟨s, ?_, davenport_box_three_even_sequence_minimal m hm heven, ?_, ?_⟩
    · intro x hx
      dsimp [davenport_box_three_even_sequence, s] at hx
      simp only [Multiset.mem_add, Multiset.mem_replicate] at hx
      have hmZ : (2 : ℤ) ≤ m := Nat.cast_le.mpr hm
      rcases hx with (((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩)
      · intro i; fin_cases i <;> simp
      · intro i; fin_cases i <;> { simp; try omega }
      · intro i; fin_cases i <;> { simp; try omega }
      · intro i; fin_cases i <;> { simp; try omega }
    · set v1 : Fin 3 → ℤ := ![-(m : ℤ), -m, -m]
      set v2 : Fin 3 → ℤ := ![-(m : ℤ), m - 1, m]
      set v3 : Fin 3 → ℤ := ![(m : ℤ), -(m - 1), m - 1]
      set v4 : Fin 3 → ℤ := ![(m : ℤ) - 1, m, -m]
      have hk1 : 4 * m ^ 3 - 6 * m ^ 2 + 4 * m - 1 ≠ 0 := by
        have : 6 * m ^ 2 ≤ 4 * m ^ 3 := by nlinarith
        have : 1 < 4 * m ^ 3 - 6 * m ^ 2 + 4 * m := by
          zify [this]
          nlinarith
        omega
      have hk2 : 4 * m ^ 3 - 4 * m ^ 2 + 2 * m ≠ 0 := by
        have : 4 * m ^ 2 < 4 * m ^ 3 := by nlinarith
        omega
      have hk3 : 4 * m ^ 3 - 2 * m ^ 2 + m ≠ 0 := by
        have : 2 * m ^ 2 < 4 * m ^ 3 := by nlinarith
        omega
      have hk4 : 4 * m ^ 3 - 4 * m ^ 2 + m ≠ 0 := by
        have : 4 * m ^ 2 < 4 * m ^ 3 := by nlinarith
        omega
      have hS : s =
          Multiset.replicate (4 * m ^ 3 - 6 * m ^ 2 + 4 * m - 1) v1 +
          Multiset.replicate (4 * m ^ 3 - 4 * m ^ 2 + 2 * m) v2 +
          Multiset.replicate (4 * m ^ 3 - 2 * m ^ 2 + m) v3 +
          Multiset.replicate (4 * m ^ 3 - 4 * m ^ 2 + m) v4 := rfl
      rw [hS]
      simp only [Multiset.toFinset_add, Multiset.toFinset_replicate,
        if_neg hk1, if_neg hk2, if_neg hk3, if_neg hk4]
      have heq : ({v1} ∪ {v2} ∪ {v3} ∪ {v4} : Finset (Fin 3 → ℤ)) = {v1, v2, v3, v4} := by
        ext x
        simp
      rw [heq]
      have h12 : v1 ≠ v2 := by intro h; have := congrFun h 1; simp [v1, v2] at this; omega
      have h13 : v1 ≠ v3 := by intro h; have := congrFun h 0; simp [v1, v3] at this; omega
      have h14 : v1 ≠ v4 := by intro h; have := congrFun h 1; simp [v1, v4] at this; omega
      have h23 : v2 ≠ v3 := by intro h; have := congrFun h 0; simp [v2, v3] at this; omega
      have h24 : v2 ≠ v4 := by intro h; have := congrFun h 2; simp [v2, v4] at this; omega
      have h34 : v3 ≠ v4 := by intro h; have := congrFun h 1; simp [v3, v4] at this; omega
      have h3 : v3 ∉ ({v4} : Finset (Fin 3 → ℤ)) := by simp [h34]
      have h2 : v2 ∉ ({v3, v4} : Finset (Fin 3 → ℤ)) := by simp [h23, h24]
      have h1 : v1 ∉ ({v2, v3, v4} : Finset (Fin 3 → ℤ)) := by simp [h12, h13, h14]
      rw [Finset.card_insert_of_notMem h1,
          Finset.card_insert_of_notMem h2,
          Finset.card_insert_of_notMem h3,
          Finset.card_singleton]
    · rw [davenport_box_three_even_sequence_card m hm]
  exact le_sSup hmem
