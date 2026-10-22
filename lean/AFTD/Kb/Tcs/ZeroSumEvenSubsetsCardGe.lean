import AFTD.Prelude

/-!
# zero_sum_even_subsets_card_ge

Topic: combinatorics   Node: dc4cc5fad99d

Provenance: helper lemma. Step toward zero_sum_w_two_le. arXiv:2610.19965 (Proofs and disproofs of some conjectures on zero-sum problems of new types), Theorem 1.2(i) w_r(2) = 2r + 1; the paper's upper bound classifies the w-bad sequences mod 4 (Theorem 3.1); this route replaces the classification by a counting argument.

For vectors a_i in Z^r indexed by a finite set, the index subsets whose sum is even in every coordinate number at least 2^{|ι| - r}.
-/

open scoped symmDiff

lemma zero_sum_even_subsets_card_ge_sum_symmDiff {ι : Type*} [DecidableEq ι]
    (f : ι → ZMod 2) (I J : Finset ι) :
    ∑ i ∈ I ∆ J, f i = ∑ i ∈ I, f i + ∑ i ∈ J, f i := by
  have hsymm : I ∆ J = (I ∪ J) \ (I ∩ J) := by
    ext x
    simp [symmDiff_def]
    tauto
  have hsub : I ∩ J ⊆ I ∪ J := Finset.inter_subset_union
  have h1 := Finset.sum_sdiff (s₁ := I ∩ J) (s₂ := I ∪ J) (f := f) hsub
  have h2 := Finset.sum_union_inter (s₁ := I) (s₂ := J) (f := f)
  rw [hsymm]
  have hC : (∑ x ∈ I ∩ J, f x) + (∑ x ∈ I ∩ J, f x) = 0 := ZModModule.add_self _
  calc
    ∑ x ∈ (I ∪ J) \ (I ∩ J), f x
        = ((∑ x ∈ (I ∪ J) \ (I ∩ J), f x) + (∑ x ∈ I ∩ J, f x)) + (∑ x ∈ I ∩ J, f x) := by
          rw [add_assoc, hC, add_zero]
    _ = (∑ x ∈ I ∪ J, f x) + (∑ x ∈ I ∩ J, f x) := by rw [h1]
    _ = ∑ x ∈ I, f x + ∑ x ∈ J, f x := h2

theorem zero_sum_even_subsets_card_ge {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (a : ι → Fin r → ℤ) :
    2 ^ Fintype.card ι ≤ 2 ^ r * ((Finset.univ : Finset (Finset ι)).filter
      (fun I => ∀ j, (2 : ℤ) ∣ ∑ i ∈ I, a i j)).card := by
  classical
  let P : Finset ι → (Fin r → ZMod 2) := fun I j => ∑ i ∈ I, (a i j : ZMod 2)
  let K : Finset (Finset ι) := (Finset.univ : Finset (Finset ι)).filter (fun I => P I = 0)
  have hK : (Finset.univ : Finset (Finset ι)).filter
      (fun I => ∀ j, (2 : ℤ) ∣ ∑ i ∈ I, a i j) = K := by
    dsimp [K]
    apply Finset.filter_congr
    intro I hI
    dsimp [P]
    constructor
    · intro h
      funext j
      change (∑ i ∈ I, (a i j : ZMod 2)) = 0
      rw [← Int.cast_sum]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h j
    · intro h j
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num]
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      rw [Int.cast_sum]
      exact congrFun h j
  rw [hK]
  have hfiber_le : ∀ v : Fin r → ZMod 2,
      ((Finset.univ : Finset (Finset ι)).filter (fun I => P I = v)).card ≤ K.card := by
    intro v
    by_cases hv : ∃ I0, P I0 = v
    · obtain ⟨I0, hI0⟩ := hv
      apply Finset.card_le_card_of_injOn (fun I => I ∆ I0)
      · intro I hI
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hI
        dsimp [K]
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        funext j
        change (∑ i ∈ I ∆ I0, (a i j : ZMod 2)) = 0
        rw [zero_sum_even_subsets_card_ge_sum_symmDiff]
        have hIv : (∑ i ∈ I, (a i j : ZMod 2)) = v j := congrFun hI j
        have hI0v : (∑ i ∈ I0, (a i j : ZMod 2)) = v j := congrFun hI0 j
        rw [hIv, hI0v]
        exact ZModModule.add_self (v j)
      · intro I hI I' hI' hEq
        exact symmDiff_left_inj.mp hEq
    · have hv' : ∀ I : Finset ι, P I ≠ v := fun I h => hv ⟨I, h⟩
      have hempty : (Finset.univ : Finset (Finset ι)).filter (fun I => P I = v) = ∅ :=
        Finset.filter_false_of_mem (by intro I hI; exact hv' I)
      rw [hempty]
      simp
  have hsum := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Finset ι)))
    (f := P) (t := (Finset.univ : Finset (Fin r → ZMod 2))) (by intro I hI; simp)
  have hcard_codomain : Fintype.card (Fin r → ZMod 2) = 2 ^ r := by
    simp [ZMod.card, Fintype.card_fin]
  calc
    2 ^ Fintype.card ι = Fintype.card (Finset ι) := by rw [Fintype.card_finset]
    _ = (Finset.univ : Finset (Finset ι)).card := by rw [Finset.card_univ]
    _ = ∑ v ∈ (Finset.univ : Finset (Fin r → ZMod 2)),
          ((Finset.univ : Finset (Finset ι)).filter (fun I => P I = v)).card := hsum
    _ ≤ ∑ v ∈ (Finset.univ : Finset (Fin r → ZMod 2)), K.card := by
          apply Finset.sum_le_sum
          intro v hv
          exact hfiber_le v
    _ = 2 ^ r * K.card := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard_codomain]
          simp
