import AFTD.Prelude
import AFTD.Kb.NumberTheory.DavenportBoxThreeOddSequence
import AFTD.Kb.NumberTheory.DavenportBoxThreeOddSequenceSum
import AFTD.Kb.NumberTheory.MultisetIsMinimalZeroSum
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# davenport_box_three_odd_sequence_minimal

Topic: elementary_number_theory   Node: e137d87deea2

Provenance: helper lemma. The core of the proof of Theorem 3 of arXiv:2610.16562 (odd m).

For m ≥ 2 odd, T(m) is a minimal zero-sum sequence: no proper nonempty subsequence sums to zero.
-/

theorem davenport_box_three_odd_sequence_minimal (m : ℕ) (hm : 2 ≤ m) (hodd : Odd m) :
    multiset_is_minimal_zero_sum (davenport_box_three_odd_sequence m) := by
  set M : ℤ := (m : ℤ) with hM
  have hM2 : 2 ≤ M := by rw [hM]; exact_mod_cast hm
  set v1 : Fin 3 → ℤ := ![-M, -M, -M] with hv1
  set v2 : Fin 3 → ℤ := ![-M, M - 1, M] with hv2
  set v3 : Fin 3 → ℤ := ![M, -M, M - 2] with hv3
  set v4 : Fin 3 → ℤ := ![M - 1, M, -M] with hv4
  set k1 := 4 * m ^ 3 - 8 * m ^ 2 + 5 * m - 2 with hk1
  set k2 := 4 * m ^ 3 - 2 * m ^ 2 + 2 * m with hk2
  set k3 := 4 * m ^ 3 - 2 * m ^ 2 + m with hk3
  set k4 := 4 * m ^ 3 - 4 * m ^ 2 + 2 * m with hk4
  have hk1Z : (k1 : ℤ) = 4 * M ^ 3 - 8 * M ^ 2 + 5 * M - 2 := by
    rw [hk1, hM]; exact davenport_box_three_odd_sequence_sum_cast1 m hm
  have hk2Z : (k2 : ℤ) = 4 * M ^ 3 - 2 * M ^ 2 + 2 * M := by
    rw [hk2, hM]; exact davenport_box_three_odd_sequence_sum_cast2 m hm
  have hk3Z : (k3 : ℤ) = 4 * M ^ 3 - 2 * M ^ 2 + M := by
    rw [hk3, hM]; exact davenport_box_three_odd_sequence_sum_cast3 m hm
  have hk4Z : (k4 : ℤ) = 4 * M ^ 3 - 4 * M ^ 2 + 2 * M := by
    rw [hk4, hM]; exact davenport_box_three_odd_sequence_sum_cast4 m hm
  have hS : davenport_box_three_odd_sequence m =
      Multiset.replicate k1 v1 + Multiset.replicate k2 v2 +
      Multiset.replicate k3 v3 + Multiset.replicate k4 v4 := rfl
  have h12 : v1 ≠ v2 := by intro h; have := congrFun h 1; simp [hv1, hv2] at this; omega
  have h13 : v1 ≠ v3 := by intro h; have := congrFun h 0; simp [hv1, hv3] at this; omega
  have h14 : v1 ≠ v4 := by intro h; have := congrFun h 1; simp [hv1, hv4] at this; omega
  have h23 : v2 ≠ v3 := by intro h; have := congrFun h 0; simp [hv2, hv3] at this; omega
  have h24 : v2 ≠ v4 := by intro h; have := congrFun h 2; simp [hv2, hv4] at this; omega
  have h34 : v3 ≠ v4 := by intro h; have := congrFun h 1; simp [hv3, hv4] at this; omega
  have hcount : ∀ (a b c d : ℕ) (x : Fin 3 → ℤ),
      (Multiset.replicate a v1 + Multiset.replicate b v2 +
       Multiset.replicate c v3 + Multiset.replicate d v4).count x =
      (if x = v1 then a else 0) + (if x = v2 then b else 0) +
      (if x = v3 then c else 0) + (if x = v4 then d else 0) := by
    intro a b c d x
    simp only [Multiset.count_add, Multiset.count_replicate,
      @eq_comm _ v1 x, @eq_comm _ v2 x, @eq_comm _ v3 x, @eq_comm _ v4 x]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hc := congrArg Multiset.card h
    dsimp [davenport_box_three_odd_sequence] at hc
    simp only [Multiset.card_add, Multiset.card_replicate] at hc
    have : 0 < 4 * m ^ 3 - 2 * m ^ 2 + 2 * m := by
      have : 2 * m ^ 2 < 4 * m ^ 3 := by nlinarith
      omega
    omega
  · exact davenport_box_three_odd_sequence_sum m hm
  · intro t ht ht0 hts
    rw [hS] at ht ⊢
    set a := t.count v1
    set b := t.count v2
    set c := t.count v3
    set d := t.count v4
    have hteq : t = Multiset.replicate a v1 + Multiset.replicate b v2 +
        Multiset.replicate c v3 + Multiset.replicate d v4 := by
      ext x
      rw [hcount]
      by_cases h1 : x = v1
      · rw [h1, if_pos rfl, if_neg h12, if_neg h13, if_neg h14]
        simp only [add_zero]
        rfl
      by_cases h2 : x = v2
      · rw [h2, if_neg h12.symm, if_pos rfl, if_neg h23, if_neg h24]
        simp only [zero_add, add_zero]
        rfl
      by_cases h3 : x = v3
      · rw [h3, if_neg h13.symm, if_neg h23.symm, if_pos rfl, if_neg h34]
        simp only [zero_add, add_zero]
        rfl
      by_cases h4 : x = v4
      · rw [h4, if_neg h14.symm, if_neg h24.symm, if_neg h34.symm, if_pos rfl]
        simp only [zero_add]
        rfl
      simp only [h1, h2, h3, h4, if_false, add_zero]
      rw [Multiset.count_eq_zero]
      intro hx
      have := Multiset.mem_of_le ht hx
      simp only [Multiset.mem_add, Multiset.mem_replicate] at this
      rcases this with (((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> contradiction
    have ha : a ≤ k1 := by
      have := Multiset.count_le_of_le v1 ht
      rwa [hcount, if_pos rfl, if_neg h12, if_neg h13, if_neg h14, add_zero, add_zero, add_zero] at this
    rw [hteq] at hts
    have he0 := congrFun hts (0 : Fin 3)
    have he1 := congrFun hts (1 : Fin 3)
    have he2 := congrFun hts (2 : Fin 3)
    simp [Multiset.sum_add, Multiset.sum_replicate, hv1, hv2, hv3, hv4] at he0 he1 he2
    set A : ℤ := (a : ℤ)
    set B : ℤ := (b : ℤ)
    set C : ℤ := (c : ℤ)
    set D : ℤ := (d : ℤ)
    set K1 : ℤ := (k1 : ℤ)
    set K2 : ℤ := (k2 : ℤ)
    set K3 : ℤ := (k3 : ℤ)
    set K4 : ℤ := (k4 : ℤ)
    have hrel2 : B * K1 = A * K2 := by
      rw [hk1Z, hk2Z]
      linear_combination (2 * M) * he0 + (2 * M ^ 2 - 3 * M + 2) * he1 + (2 * M ^ 2 - M) * he2
    have hrel3 : C * K1 = A * K3 := by
      rw [hk1Z, hk3Z]
      linear_combination (2 * M ^ 2 - M) * he0 + M * he1 + (2 * M ^ 2 - 2 * M + 1) * he2
    have hrel4 : D * K1 = A * K4 := by
      rw [hk1Z, hk4Z]
      linear_combination (2 * M ^ 2 - 3 * M + 2) * he0 + (2 * M ^ 2 - 2 * M) * he1 + M * he2
    obtain ⟨j, hj⟩ : ∃ j : ℤ, M = 2 * j + 1 := by
      obtain ⟨j, rfl⟩ := hodd
      use (j : ℤ)
      rw [hM]
      push_cast
      ring
    set c1 : ℤ := j
    set c2 : ℤ := 1 - j * (4 * M ^ 2 - 8 * M + 5)
    set c3 : ℤ := -c2
    have hbez : c1 * K1 + c2 * K2 + c3 * K3 = 1 := by
      dsimp [c1, c2, c3]
      rw [hk1Z, hk2Z, hk3Z, hj]
      ring
    have hAK1 : A = K1 * (c1 * A + c2 * B + c3 * C) := by
      calc
        A = A * 1 := by ring
        _ = A * (c1 * K1 + c2 * K2 + c3 * K3) := by rw [hbez]
        _ = c1 * A * K1 + c2 * (A * K2) + c3 * (A * K3) := by ring
        _ = c1 * A * K1 + c2 * (B * K1) + c3 * (C * K1) := by rw [← hrel2, ← hrel3]
        _ = K1 * (c1 * A + c2 * B + c3 * C) := by ring
    have hK1pos : 0 < K1 := by
      rw [hk1Z]
      have : 4 * M ^ 3 - 8 * M ^ 2 + 5 * M - 2 = 4 * M ^ 2 * (M - 2) + 5 * M - 2 := by ring
      rw [this]
      have h1 : 0 ≤ M - 2 := by linarith
      have h2 : 0 ≤ 4 * M ^ 2 := by nlinarith
      have h3 : 0 ≤ 4 * M ^ 2 * (M - 2) := mul_nonneg h2 h1
      linarith
    have hK1ne : K1 ≠ 0 := by linarith
    set q : ℤ := c1 * A + c2 * B + c3 * C
    have hq0 : 0 ≤ q := by
      have : 0 ≤ A := Nat.cast_nonneg a
      have : 0 ≤ K1 * q := by rw [← hAK1]; exact this
      nlinarith
    have hq1 : q ≤ 1 := by
      have : A ≤ K1 := Nat.cast_le.mpr ha
      have : K1 * q ≤ K1 * 1 := by rw [← hAK1]; linarith
      nlinarith
    rcases (show q = 0 ∨ q = 1 by omega) with hq | hq
    · exfalso
      apply ht0
      have hA0 : A = 0 := by rw [hAK1, hq]; ring
      have hB0 : B = 0 := by
        have : B * K1 = 0 := by rw [hrel2, hA0, zero_mul]
        exact mul_eq_zero.mp this |>.resolve_right hK1ne
      have hC0 : C = 0 := by
        have : C * K1 = 0 := by rw [hrel3, hA0, zero_mul]
        exact mul_eq_zero.mp this |>.resolve_right hK1ne
      have hD0 : D = 0 := by
        have : D * K1 = 0 := by rw [hrel4, hA0, zero_mul]
        exact mul_eq_zero.mp this |>.resolve_right hK1ne
      have ha0 : a = 0 := Nat.cast_eq_zero.mp hA0
      have hb0 : b = 0 := Nat.cast_eq_zero.mp hB0
      have hc0 : c = 0 := Nat.cast_eq_zero.mp hC0
      have hd0 : d = 0 := Nat.cast_eq_zero.mp hD0
      rw [hteq, ha0, hb0, hc0, hd0]
      simp
    · have hA1 : A = K1 := by rw [hAK1, hq]; ring
      have hB1 : B = K2 := by
        have : B * K1 = K2 * K1 := by rw [hrel2, hA1, mul_comm]
        exact mul_right_cancel₀ hK1ne this
      have hC1 : C = K3 := by
        have : C * K1 = K3 * K1 := by rw [hrel3, hA1, mul_comm]
        exact mul_right_cancel₀ hK1ne this
      have hD1 : D = K4 := by
        have : D * K1 = K4 * K1 := by rw [hrel4, hA1, mul_comm]
        exact mul_right_cancel₀ hK1ne this
      have ha1 : a = k1 := Nat.cast_inj.mp hA1
      have hb1 : b = k2 := Nat.cast_inj.mp hB1
      have hc1 : c = k3 := Nat.cast_inj.mp hC1
      have hd1 : d = k4 := Nat.cast_inj.mp hD1
      rw [hteq, ha1, hb1, hc1, hd1]
