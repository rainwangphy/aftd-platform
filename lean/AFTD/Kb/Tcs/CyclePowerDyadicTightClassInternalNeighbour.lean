import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_tight_class_internal_neighbour

Topic: combinatorics   Node: d642420e5bae

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

Every selected nonendpoint offset of a tight dyadic class has a selected incident dyadic edge at some positive rank below its exponent.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_tight_class_internal_neighbour
    (m : ℕ) (hm : 1 ≤ m) (b : ℕ → Bool)
    (htight : cycle_power_dyadic_class_weight m b =
      (range (2^m)).sum (fun i => (b i).toNat))
    (a : ℕ) (ha₀ : 0 < a) (haD : a < 2^m-1) (hba : b a = true) :
    ∃ j, 1 ≤ j ∧ j < m ∧ ∃ i < 2^j,
      b i = true ∧ b (i+2^m-2^j) = true ∧ (a = i ∨ a = i+2^m-2^j) := by
  classical
  by_contra hn
  let c : ℕ → Bool := fun i => if i = a then false else b i
  have he₀ : c 0 = b 0 := by
    have hne : (0 : ℕ) ≠ a := by omega
    simp only [c, if_neg hne]
  have he₁ : c (2^m-1) = b (2^m-1) := by simp [c, ne_of_gt haD]
  have hpairs : ∀ j, 1 ≤ j → j < m → ∀ i < 2^j,
      (c i && c (i+2^m-2^j)) = (b i && b (i+2^m-2^j)) := by
    intro j hj hjm i hi
    by_cases hia : i = a
    · have hbi : b i = true := hia.symm ▸ hba
      have hhigh : b (i+2^m-2^j) = false := by
        apply Bool.eq_false_iff.mpr
        intro hbhi
        exact hn ⟨j, hj, hjm, i, hi, hbi, hbhi, Or.inl hia.symm⟩
      have hne : i+2^m-2^j ≠ a := by
        intro h
        have := h.symm ▸ hba
        rw [hhigh] at this
        contradiction
      simp only [c, if_pos hia, if_neg hne, hhigh, Bool.false_and, Bool.and_false]
    · by_cases hhigha : i+2^m-2^j = a
      · have hbhi : b (i+2^m-2^j) = true := hhigha.symm ▸ hba
        have hlow : b i = false := by
          apply Bool.eq_false_iff.mpr
          intro hbi
          exact hn ⟨j, hj, hjm, i, hi, hbi, hbhi, Or.inr hhigha.symm⟩
        simp only [c, if_neg hia, if_pos hhigha, hlow, Bool.false_and]
      · simp only [c, if_neg hia, if_neg hhigha]
  have hweight : cycle_power_dyadic_class_weight m c = cycle_power_dyadic_class_weight m b := by
    unfold cycle_power_dyadic_class_weight
    rw [he₀, he₁]
    congr 1
    apply sum_congr rfl
    intro j hj
    by_cases hj₀ : j = 0
    · simp only [if_pos hj₀]
    · simp only [if_neg hj₀]
      apply sum_congr rfl
      intro i hi
      rw [hpairs j (by omega) (mem_range.mp hj) i (mem_range.mp hi)]
  have hpoint (i : ℕ) : (c i).toNat + (if i = a then 1 else 0) = (b i).toNat := by
    by_cases hi : i = a
    · subst i
      simp [c, hba]
    · simp only [c, if_neg hi, add_zero]
  have hsum : (range (2^m)).sum (fun i => (c i).toNat) + 1 =
      (range (2^m)).sum (fun i => (b i).toNat) := by
    have hs := sum_congr rfl (fun i (hi : i ∈ range (2^m)) => hpoint i)
    simpa only [sum_add_distrib, sum_ite_eq', mem_range.mpr (by omega : a < 2^m),
      if_true] using hs
  have hle := cycle_power_dyadic_class_weight_le m hm c
  omega
