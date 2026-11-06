import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FourTypeSimultaneousBalanceCounts

/-!
# two_finite_subsets_simultaneously_balanced

Topic: fair_division   Node: 5bdb66461625

Provenance: helper lemma. Finite balancing lemma for the two-agent bivalued rounding argument in IN-570.

Given two subsets of a finite set, one can split the underlying set into two parts so that the two part sizes and the counts of elements from each subset differ by at most one.
-/

theorem two_finite_subsets_simultaneously_balanced
    (m : ℕ) (A B : Finset (Fin m)) :
    ∃ S : Finset (Fin m),
      S.card ≤ (m + 1) / 2 ∧
      (Finset.univ \ S).card ≤ (m + 1) / 2 ∧
      (S ∩ A).card ≤ (A.card + 1) / 2 ∧
      (A \ S).card ≤ (A.card + 1) / 2 ∧
      (S ∩ B).card ≤ (B.card + 1) / 2 ∧
      (B \ S).card ≤ (B.card + 1) / 2 := by
  classical
  let R0 : Finset (Fin m) := (Finset.univ \ A) \ B
  let R1 : Finset (Fin m) := (Finset.univ \ A) ∩ B
  let R2 : Finset (Fin m) := A \ B
  let R3 : Finset (Fin m) := A ∩ B
  have d01 : Disjoint R0 R1 := by
    apply Finset.disjoint_left.mpr
    intro t hi hj
    simp only [R0, R1, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_univ, true_and] at hi hj
    tauto
  have d02 : Disjoint R0 R2 := by
    apply Finset.disjoint_left.mpr
    intro t hi hj
    simp only [R0, R2, Finset.mem_sdiff,
      Finset.mem_univ, true_and] at hi hj
    tauto
  have d03 : Disjoint R0 R3 := by
    apply Finset.disjoint_left.mpr
    intro t hi hj
    simp only [R0, R3, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_univ, true_and] at hi hj
    tauto
  have d12 : Disjoint R1 R2 := by
    apply Finset.disjoint_left.mpr
    intro t hi hj
    simp only [R1, R2, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_univ, true_and] at hi hj
    tauto
  have d13 : Disjoint R1 R3 := by
    apply Finset.disjoint_left.mpr
    intro t hi hj
    simp only [R1, R3, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_univ, true_and] at hi hj
    tauto
  have d23 : Disjoint R2 R3 := by
    apply Finset.disjoint_left.mpr
    intro t hi hj
    simp only [R2, R3, Finset.mem_sdiff, Finset.mem_inter] at hi hj
    tauto
  obtain ⟨w, x, y, z, hw, hx, hy, hz, htot, htotc, hB, hBc, hA, hAc⟩ :=
    four_type_simultaneous_balance_counts R0.card R1.card R2.card R3.card
  obtain ⟨W, hW, hWc⟩ := Finset.exists_subset_card_eq hw
  obtain ⟨X, hX, hXc⟩ := Finset.exists_subset_card_eq hx
  obtain ⟨Y, hY, hYc⟩ := Finset.exists_subset_card_eq hy
  obtain ⟨Z, hZ, hZc⟩ := Finset.exists_subset_card_eq hz
  have dWX : Disjoint W X := d01.mono hW hX
  have dWY : Disjoint W Y := d02.mono hW hY
  have dWZ : Disjoint W Z := d03.mono hW hZ
  have dXY : Disjoint X Y := d12.mono hX hY
  have dXZ : Disjoint X Z := d13.mono hX hZ
  have dYZ : Disjoint Y Z := d23.mono hY hZ
  let S := W ∪ X ∪ Y ∪ Z
  have hSc : S.card = w + x + y + z := by
    simp [S, Finset.card_union_of_disjoint,
      dWX, dWY, dWZ, dXY, dXZ, dYZ, hWc, hXc, hYc, hZc, Nat.add_assoc]
  have hR : R0 ∪ R1 ∪ R2 ∪ R3 = Finset.univ := by
    ext t
    simp only [R0, R1, R2, R3, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_union, Finset.mem_univ, true_and, iff_true]
    tauto
  have hRc : R0.card + R1.card + R2.card + R3.card = m := by
    have hc := congrArg Finset.card hR
    simp [Finset.card_union_of_disjoint,
      d01, d02, d03, d12, d13, d23] at hc
    simpa [Nat.add_assoc] using hc
  have hAR : A = R2 ∪ R3 := by
    ext t
    simp only [R2, R3, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
    tauto
  have hBR : B = R1 ∪ R3 := by
    ext t
    simp only [R1, R3, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_univ,
      Finset.mem_union, true_and]
    tauto
  have hAc' : A.card = R2.card + R3.card := by rw [hAR, Finset.card_union_of_disjoint d23]
  have hBc' : B.card = R1.card + R3.card := by rw [hBR, Finset.card_union_of_disjoint d13]
  have hSA : S ∩ A = Y ∪ Z := by
    ext t
    have hw' : t ∈ W → t ∈ R0 := fun ht => hW ht
    have hx' : t ∈ X → t ∈ R1 := fun ht => hX ht
    have hy' : t ∈ Y → t ∈ R2 := fun ht => hY ht
    have hz' : t ∈ Z → t ∈ R3 := fun ht => hZ ht
    simp only [R0, R1, R2, R3, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_univ, true_and] at hw' hx' hy' hz'
    simp only [S, Finset.mem_inter, Finset.mem_union]
    tauto
  have hSB : S ∩ B = X ∪ Z := by
    ext t
    have hw' : t ∈ W → t ∈ R0 := fun ht => hW ht
    have hx' : t ∈ X → t ∈ R1 := fun ht => hX ht
    have hy' : t ∈ Y → t ∈ R2 := fun ht => hY ht
    have hz' : t ∈ Z → t ∈ R3 := fun ht => hZ ht
    simp only [R0, R1, R2, R3, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_univ, true_and] at hw' hx' hy' hz'
    simp only [S, Finset.mem_inter, Finset.mem_union]
    tauto
  have hSAc : (S ∩ A).card = y + z := by
    rw [hSA, Finset.card_union_of_disjoint dYZ, hYc, hZc]
  have hSBc : (S ∩ B).card = x + z := by
    rw [hSB, Finset.card_union_of_disjoint dXZ, hXc, hZc]
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hSc, ← hRc]; exact htot
  · rw [Finset.card_sdiff, Finset.card_univ, Finset.inter_univ, Fintype.card_fin, hSc, ← hRc]
    omega
  · rw [hSAc, hAc']; exact hA
  · rw [Finset.card_sdiff, hSAc, hAc']
    omega
  · rw [hSBc, hBc']; exact hB
  · rw [Finset.card_sdiff, hSBc, hBc']
    omega
