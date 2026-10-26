import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_dyadic_tight_class_spanning

Topic: combinatorics   Node: 8fa36f03e933

Provenance: helper lemma. Uniform route for OP-205 and RT-1, arXiv:2610.15635 Section 3. Existing k=3,7,15 weight certificates suggest this dyadic tree. The sparse distance graph is obtained recursively by attaching one leaf to every vertex; tight classes are connected subtrees containing the distinguished endpoint edge.

A nonempty subset attaining equality in the uniform dyadic weight bound contains both endpoints of its arc.
-/

lemma cycle_power_dyadic_tight_class_spanning_aux (k : ℕ) :
    ∀ (b : ℕ → Bool),
      cycle_power_dyadic_class_weight (k + 1) b = ∑ i ∈ Finset.range (2 ^ (k + 1)), (b i).toNat →
      (∃ i < 2 ^ (k + 1), b i = true) →
      b 0 = true ∧ b (2 ^ (k + 1) - 1) = true := by
  induction' k with k ih
  · intro b hw hne
    have hw' : 2 * (b 0 && b 1).toNat = (b 0).toNat + (b 1).toNat := by
      have h1 : cycle_power_dyadic_class_weight 1 b = 2 * (b 0 && b 1).toNat := by
        dsimp [cycle_power_dyadic_class_weight]; simp
      have h2 : (Finset.range (2 ^ 1)).sum (fun i => (b i).toNat) = (b 0).toNat + (b 1).toNat := by
        simp [Finset.sum_range_succ]
      linarith [hw, h1, h2]
    obtain ⟨i, hi, hbi⟩ := hne
    have h0 : b 0 = true := by
      by_contra h
      have hb0 : b 0 = false := Bool.eq_false_iff.2 h
      have hb1 : b 1 = true := by
        interval_cases i
        · rw [hb0] at hbi; contradiction
        · exact hbi
      rw [hb0, hb1] at hw'
      revert hw'; decide
    have h1 : b 1 = true := by
      by_contra h
      have hb1 : b 1 = false := Bool.eq_false_iff.2 h
      rw [h0, hb1] at hw'
      revert hw'; decide
    exact ⟨h0, h1⟩
  · intro b hw hne
    let b_lift := cycle_power_dyadic_b_lift k b
    have h_split := cycle_power_dyadic_class_weight_succ k b
    have h_le1 := cycle_power_dyadic_class_weight_le_aux k b_lift
    have h_le2 := cycle_power_dyadic_sum_lift_and_cross_le k b
    have hw_lift : cycle_power_dyadic_class_weight (k + 1) b_lift =
        ∑ i ∈ Finset.range (2 ^ (k + 1)), (b_lift i).toNat := by
      linarith [hw, h_split, h_le1, h_le2]
    have hne_lift : ∃ j < 2 ^ (k + 1), b_lift j = true := by
      by_contra h
      have hall : ∀ j < 2 ^ (k + 1), b_lift j = false := by
        intro j hj
        have : ¬ (b_lift j = true) := fun ht => h ⟨j, hj, ht⟩
        exact Bool.eq_false_iff.2 this
      have h_cross : ∀ j < 2 ^ (k + 1), (b j && b (j + 2 ^ (k + 1))) = false := by
        intro j hj
        dsimp [b_lift, cycle_power_dyadic_b_lift] at hall
        have hj_lift := hall j hj
        split_ifs at hj_lift with h_lt
        · rw [hj_lift]; rfl
        · rw [hj_lift]; cases b j <;> rfl
      have s1 : ∑ i ∈ Finset.range (2 ^ (k + 1)), (b_lift i).toNat = 0 := by
        rw [Finset.sum_congr rfl (fun x hx => by rw [hall x (Finset.mem_range.1 hx), Bool.toNat_false])]
        simp
      have s2 : ∑ i ∈ Finset.range (2 ^ (k + 1)), (b i && b (i + 2 ^ (k + 1))).toNat = 0 := by
        rw [Finset.sum_congr rfl (fun x hx => by rw [h_cross x (Finset.mem_range.1 hx), Bool.toNat_false])]
        simp
      obtain ⟨i, hi, hbi⟩ := hne
      have h_sum_pos : 1 ≤ ∑ x ∈ Finset.range (2 ^ (k + 2)), (b x).toNat := by
        calc 1 = (b i).toNat := by rw [hbi, Bool.toNat_true]
        _ ≤ ∑ x ∈ Finset.range (2 ^ (k + 2)), (b x).toNat :=
          Finset.single_le_sum (f := fun x => (b x).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hi)
      linarith [hw, h_split, h_le1, s1, s2, h_sum_pos]
    have ih_res := ih b_lift hw_lift hne_lift
    have h0_lift : b_lift 0 = b 0 := by
      dsimp [b_lift, cycle_power_dyadic_b_lift]
      have : 0 < 2 ^ k := Nat.two_pow_pos k
      simp [this]
    have hlast_lift : b_lift (2 ^ (k + 1) - 1) = b (2 ^ (k + 2) - 1) := by
      dsimp [b_lift, cycle_power_dyadic_b_lift]
      have hge : ¬ (2 ^ (k + 1) - 1 < 2 ^ k) := by
        rw [pow_succ]
        have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        omega
      simp only [if_neg hge]
      congr 1
      have : 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by
        rw [pow_succ, mul_two]
      have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      omega
    rw [h0_lift] at ih_res
    rw [hlast_lift] at ih_res
    exact ih_res

theorem cycle_power_dyadic_tight_class_spanning (m : ℕ) (hm : 1 ≤ m) (b : ℕ → Bool)
    (hw : cycle_power_dyadic_class_weight m b =
      (Finset.range (2 ^ m)).sum (fun i => (b i).toNat))
    (hne : ∃ i < 2 ^ m, b i = true) : b 0 = true ∧ b (2 ^ m - 1) = true := by
  have h : m = (m - 1) + 1 := (Nat.sub_add_cancel hm).symm
  rw [h] at hw hne ⊢
  exact cycle_power_dyadic_tight_class_spanning_aux (m - 1) b hw hne
