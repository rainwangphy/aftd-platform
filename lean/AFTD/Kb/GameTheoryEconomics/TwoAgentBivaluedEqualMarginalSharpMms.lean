import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEqualMarginalLottery
import AFTD.Kb.GameTheoryEconomics.IsScaledBivaluedChores
import AFTD.Kb.GameTheoryEconomics.IsExPostAlphaMmsChores
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# two_agent_bivalued_equal_marginal_sharp_mms

Topic: fair_division   Node: 0fa2ff6d9db5

Provenance: original. Related work: Two-agent partial case of the proposed problem OP-1112. Related work: https://arxiv.org/abs/2609.35280, Sections 3.1 and 5.4, establishes the general equal-marginal 3/2 bound and its lower bound at cost ratio 2.

For two agents (n = 2), ratio r with 1 ≤ r and r ≤ 2, and m chores with a cost profile c : Fin 2 → Fin m → ℝ satisfying is_scaled_bivalued_chores r c, there exists a lottery p ∈ stdSimplex ℝ (Fin m → Fin 2) such that is_equal_marginal_lottery p and is_ex_post_alpha_mms_chores ((r+1)/2) c p.
-/

private lemma in570_even_arithmetic (k h : ℕ) (d : ℝ) (hk : 1 ≤ k) (hd : 0 ≤ d) :
    (k : ℝ) + d * (((h + 1) / 2 : ℕ) : ℝ) ≤
      (1 + d / 2) * ((k : ℝ) + d * (h : ℝ) / 2) := by
  have hc : 2 * ((h + 1) / 2) ≤ h + 1 := by omega
  have hcr : (2 : ℝ) * (((h + 1) / 2 : ℕ) : ℝ) ≤ (h : ℝ) + 1 := by
    exact_mod_cast hc
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have harr : 0 ≤ (k : ℝ) + (h : ℝ) - 2 * (((h + 1) / 2 : ℕ) : ℝ) := by linarith
  have hmul := mul_nonneg hd harr
  have hsq : 0 ≤ d * d * (h : ℝ) := by positivity
  nlinarith

private lemma in570_odd_arithmetic (k h : ℕ) (d : ℝ) (hd : 0 ≤ d) :
    (k + 1 : ℝ) + d * (((h + 1) / 2 : ℕ) : ℝ) ≤
      (1 + d / 2) * ((k + 1 : ℝ) + d * ((h - k : ℕ) : ℝ)) := by
  have hc : 2 * ((h + 1) / 2) ≤ k + 1 + 2 * (h - k) := by omega
  have hcr : (2 : ℝ) * (((h + 1) / 2 : ℕ) : ℝ) ≤
      (k : ℝ) + 1 + 2 * ((h - k : ℕ) : ℝ) := by
    exact_mod_cast hc
  have harr : 0 ≤ (k : ℝ) + 1 + 2 * ((h - k : ℕ) : ℝ) -
      2 * (((h + 1) / 2 : ℕ) : ℝ) := by linarith
  have hmul := mul_nonneg hd harr
  have hsq : 0 ≤ d * d * ((h - k : ℕ) : ℝ) := by positivity
  nlinarith


private lemma in570_four_type_counts (a b c d : ℕ) :
    ∃ w x y z : ℕ,
      w ≤ a ∧ x ≤ b ∧ y ≤ c ∧ z ≤ d ∧
      w+x+y+z ≤ (a+b+c+d+1)/2 ∧
      (a-w)+(b-x)+(c-y)+(d-z) ≤ (a+b+c+d+1)/2 ∧
      x+z ≤ (b+d+1)/2 ∧ (b-x)+(d-z) ≤ (b+d+1)/2 ∧
      y+z ≤ (c+d+1)/2 ∧ (c-y)+(d-z) ≤ (c+d+1)/2 := by
  have ha : a % 2 < 2 := Nat.mod_lt _ (by omega)
  have hb : b % 2 < 2 := Nat.mod_lt _ (by omega)
  have hc : c % 2 < 2 := Nat.mod_lt _ (by omega)
  have hd : d % 2 < 2 := Nat.mod_lt _ (by omega)
  interval_cases hma : a % 2 <;> interval_cases hmb : b % 2 <;>
    interval_cases hmc : c % 2 <;> interval_cases hmd : d % 2 <;>
    first
    | refine ⟨a / 2, b / 2, c / 2, d / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨a / 2, b / 2, c / 2, (d + 1) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨a / 2, b / 2, (c + 1) / 2, d / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨a / 2, b / 2, (c + 1) / 2, (d + 1) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨a / 2, (b + 1) / 2, c / 2, d / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨a / 2, (b + 1) / 2, c / 2, (d + 1) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨a / 2, (b + 1) / 2, (c + 1) / 2, d / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨a / 2, (b + 1) / 2, (c + 1) / 2, (d + 1) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨(a + 1) / 2, b / 2, c / 2, d / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨(a + 1) / 2, b / 2, c / 2, (d + 1) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨(a + 1) / 2, b / 2, (c + 1) / 2, d / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨(a + 1) / 2, b / 2, (c + 1) / 2, (d + 1) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨(a + 1) / 2, (b + 1) / 2, c / 2, d / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨(a + 1) / 2, (b + 1) / 2, c / 2, (d + 1) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨(a + 1) / 2, (b + 1) / 2, (c + 1) / 2, d / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨(a + 1) / 2, (b + 1) / 2, (c + 1) / 2, (d + 1) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega


private lemma in570_balance_two_subsets (m : ℕ) (A B : Finset (Fin m)) :
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
    simp only [R0, R1, R2, R3, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_univ, true_and] at hi hj
    tauto
  have d02 : Disjoint R0 R2 := by
    apply Finset.disjoint_left.mpr
    intro t hi hj
    simp only [R0, R1, R2, R3, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_univ, true_and] at hi hj
    tauto
  have d03 : Disjoint R0 R3 := by
    apply Finset.disjoint_left.mpr
    intro t hi hj
    simp only [R0, R1, R2, R3, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_univ, true_and] at hi hj
    tauto
  have d12 : Disjoint R1 R2 := by
    apply Finset.disjoint_left.mpr
    intro t hi hj
    simp only [R0, R1, R2, R3, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_univ, true_and] at hi hj
    tauto
  have d13 : Disjoint R1 R3 := by
    apply Finset.disjoint_left.mpr
    intro t hi hj
    simp only [R0, R1, R2, R3, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_univ, true_and] at hi hj
    tauto
  have d23 : Disjoint R2 R3 := by
    apply Finset.disjoint_left.mpr
    intro t hi hj
    simp only [R0, R1, R2, R3, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_univ, true_and] at hi hj
    tauto
  obtain ⟨w, x, y, z, hw, hx, hy, hz, htot, htotc, hB, hBc, hA, hAc⟩ :=
    in570_four_type_counts R0.card R1.card R2.card R3.card
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
  have hSc : S.card = w+x+y+z := by
    simp [S, Finset.card_union_of_disjoint, Finset.disjoint_union_left,
      dWX, dWY, dWZ, dXY, dXZ, dYZ, hWc, hXc, hYc, hZc, Nat.add_assoc]
  have hR : R0 ∪ R1 ∪ R2 ∪ R3 = Finset.univ := by
    ext t
    simp only [R0, R1, R2, R3, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_union, Finset.mem_univ, true_and, iff_true]
    tauto
  have hRc : R0.card + R1.card + R2.card + R3.card = m := by
    have hc := congrArg Finset.card hR
    simp [Finset.card_union_of_disjoint, Finset.disjoint_union_left,
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
  · omega
  · rw [Finset.card_sdiff]
    simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hSc]
    omega
  · omega
  · rw [Finset.card_sdiff, hSAc, hAc']
    omega
  · omega
  · rw [Finset.card_sdiff, hSBc, hBc']
    omega


private lemma in570_bivalued_sum (m : ℕ) (r a : ℝ) (u : Fin m → ℝ)
    (H S : Finset (Fin m)) (hu : ∀ g, u g = if g ∈ H then r * a else a) :
    additive_valuation u S =
      a * ((S.card : ℝ) + (r - 1) * ((S ∩ H).card : ℝ)) := by
  classical
  have hc : ((S \ H).card : ℝ) + ((S ∩ H).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_inter S H
  simp only [additive_valuation, hu, Finset.sum_ite, Finset.sum_const,
    Finset.filter_mem_eq_inter, Finset.filter_notMem_eq_sdiff, nsmul_eq_mul]
  rw [← hc]
  ring


private lemma in570_total_half_le_mms (m : ℕ) (u : Fin m → ℝ) :
    (∑ g : Fin m, u g) / 2 ≤ chore_maximin_share 2 u := by
  simp only [chore_maximin_share]
  refine le_ciInf fun P => ?_
  have hbdd : BddAbove (Set.range fun k : Fin 2 => additive_valuation u (bundle_of P k)) :=
    (Set.finite_range _).bddAbove
  have hsum : ∑ k : Fin 2, additive_valuation u (bundle_of P k) = ∑ g : Fin m, u g := by
    have h := Finset.sum_fiberwise (Finset.univ : Finset (Fin m)) P u
    simpa [bundle_of, additive_valuation] using h
  have h0 := le_ciSup hbdd (0 : Fin 2)
  have h1 := le_ciSup hbdd (1 : Fin 2)
  rw [Fin.sum_univ_two] at hsum
  linarith


private lemma in570_odd_mms_lower (k : ℕ) (r a : ℝ) (hr : 1 ≤ r) (ha : 0 < a)
    (u : Fin (2*k+1) → ℝ) (H : Finset (Fin (2*k+1)))
    (hu : ∀ g, u g = if g ∈ H then r * a else a) :
    a * ((k + 1 : ℝ) + (r - 1) * ((H.card - k : ℕ) : ℝ)) ≤
      chore_maximin_share 2 u := by
  classical
  have hlarge (S : Finset (Fin (2*k+1))) (hbig : k + 1 ≤ S.card) :
      a * ((k + 1 : ℝ) + (r - 1) * ((H.card - k : ℕ) : ℝ)) ≤
        additive_valuation u S := by
    have hcomp : ((Finset.univ : Finset (Fin (2*k+1))) \ S).card ≤ k := by
      rw [Finset.card_sdiff]
      simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      omega
    have hsub : H \ S ⊆ (Finset.univ : Finset (Fin (2*k+1))) \ S := by
      intro g hg
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hg ⊢
      exact hg.2
    have hle := Finset.card_le_card hsub
    have hc : (H \ S).card + (S ∩ H).card = H.card := by
      simpa [Finset.inter_comm] using Finset.card_sdiff_add_card_inter H S
    have hh : H.card - k ≤ (S ∩ H).card := by omega
    have hbig' : (k + 1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hbig
    have hh' : ((H.card - k : ℕ) : ℝ) ≤ ((S ∩ H).card : ℝ) := by exact_mod_cast hh
    have hval : (k + 1 : ℝ) + (r - 1) * ((H.card - k : ℕ) : ℝ) ≤
        (S.card : ℝ) + (r - 1) * ((S ∩ H).card : ℝ) := by
      gcongr
    rw [in570_bivalued_sum (2*k+1) r a u H S hu]
    exact mul_le_mul_of_nonneg_left hval (le_of_lt ha)
  simp only [chore_maximin_share]
  refine le_ciInf fun P => ?_
  have hsum : (bundle_of P 0).card + (bundle_of P 1).card = 2*k+1 := by
    have hh := Finset.sum_fiberwise (Finset.univ : Finset (Fin (2*k+1))) P (fun _ => (1 : ℕ))
    simpa [bundle_of, Fin.sum_univ_two] using hh
  have hex : ∃ i : Fin 2, k + 1 ≤ (bundle_of P i).card := by
    by_cases h0 : k + 1 ≤ (bundle_of P 0).card
    · exact ⟨0, h0⟩
    · exact ⟨1, by omega⟩
  obtain ⟨i, hi⟩ := hex
  have hbdd : BddAbove (Set.range fun i : Fin 2 => additive_valuation u (bundle_of P i)) :=
    (Set.finite_range _).bddAbove
  exact le_trans (hlarge (bundle_of P i) hi) (le_ciSup hbdd i)


private lemma in570_balanced_cost_upper (m : ℕ) (r a : ℝ) (hr : 1 ≤ r) (ha : 0 < a)
    (u : Fin m → ℝ) (H S : Finset (Fin m))
    (hu : ∀ g, u g = if g ∈ H then r * a else a)
    (hs : S.card ≤ (m + 1) / 2)
    (hh : (S ∩ H).card ≤ (H.card + 1) / 2) :
    additive_valuation u S ≤ a * ((((m + 1) / 2 : ℕ) : ℝ) +
      (r - 1) * (((H.card + 1) / 2 : ℕ) : ℝ)) := by
  have hs' : (S.card : ℝ) ≤ (((m + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hs
  have hh' : ((S ∩ H).card : ℝ) ≤ (((H.card + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hh
  rw [in570_bivalued_sum m r a u H S hu]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt ha)
  have hh'' := mul_le_mul_of_nonneg_left hh' (sub_nonneg.mpr hr)
  linarith


private lemma in570_balanced_upper_le_mms (m : ℕ) (r a : ℝ) (hr : 1 ≤ r) (ha : 0 < a)
    (u : Fin m → ℝ) (H : Finset (Fin m))
    (hu : ∀ g, u g = if g ∈ H then r * a else a) :
    a * ((((m + 1) / 2 : ℕ) : ℝ) +
      (r - 1) * (((H.card + 1) / 2 : ℕ) : ℝ)) ≤
      ((r + 1) / 2) * chore_maximin_share 2 u := by
  classical
  have hd : 0 ≤ r - 1 := by linarith
  have halpha : 0 ≤ (r + 1) / 2 := by linarith
  have hu0 : ∀ g, 0 ≤ u g := by
    intro g
    rw [hu g]
    split_ifs <;> positivity
  have hmms : 0 ≤ chore_maximin_share 2 u := by
    have ht := in570_total_half_le_mms m u
    have hn : 0 ≤ ∑ g : Fin m, u g := Finset.sum_nonneg (fun g _ => hu0 g)
    linarith
  by_cases hz : m = 0
  · have hc : H.card = 0 := by
      have hh := Finset.card_le_univ H
      simp only [Fintype.card_fin, hz] at hh
      omega
    simp only [hz, hc, Nat.zero_add, Nat.reduceDiv, Nat.cast_zero, mul_zero, add_zero]
    exact mul_nonneg halpha hmms
  obtain ⟨k, hke | hko⟩ : ∃ k : ℕ, m = 2*k ∨ m = 2*k+1 := ⟨m/2, by omega⟩
  · subst m
    have hk : 1 ≤ k := by omega
    have hceil : (2*k+1)/2 = k := by omega
    have hsum : (∑ g : Fin (2*k), u g) =
        a * (2 * (k : ℝ) + (r - 1) * (H.card : ℝ)) := by
      have hs := in570_bivalued_sum (2*k) r a u H Finset.univ hu
      simpa [additive_valuation, Finset.card_univ, Fintype.card_fin,
        Nat.cast_mul] using hs
    have hhalf : a * ((k : ℝ) + (r - 1) * (H.card : ℝ) / 2) ≤
        chore_maximin_share 2 u := by
      calc
        a * ((k : ℝ) + (r - 1) * (H.card : ℝ) / 2) =
            (a * (2 * (k : ℝ) + (r - 1) * (H.card : ℝ))) / 2 := by ring
        _ = (∑ g : Fin (2*k), u g) / 2 := by rw [hsum]
        _ ≤ chore_maximin_share 2 u := in570_total_half_le_mms (2*k) u
    have hround := in570_even_arithmetic k H.card (r - 1) hk hd
    rw [hceil]
    calc
      a * ((k : ℝ) + (r - 1) * (((H.card + 1) / 2 : ℕ) : ℝ)) ≤
          a * ((1 + (r - 1) / 2) * ((k : ℝ) + (r - 1) * (H.card : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hround (le_of_lt ha)
      _ = ((r + 1) / 2) * (a * ((k : ℝ) + (r - 1) * (H.card : ℝ) / 2)) := by ring
      _ ≤ ((r + 1) / 2) * chore_maximin_share 2 u :=
        mul_le_mul_of_nonneg_left hhalf halpha
  · subst m
    have hceil : (2*k+1+1)/2 = k+1 := by omega
    have hround := in570_odd_arithmetic k H.card (r - 1) hd
    have hlower := in570_odd_mms_lower k r a hr ha u H hu
    rw [hceil]
    simp only [Nat.cast_add, Nat.cast_one]
    calc
      a * ((k + 1 : ℝ) + (r - 1) * (((H.card + 1) / 2 : ℕ) : ℝ)) ≤
          a * ((1 + (r - 1) / 2) * ((k + 1 : ℝ) + (r - 1) * ((H.card - k : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hround (le_of_lt ha)
      _ = ((r + 1) / 2) * (a * ((k + 1 : ℝ) + (r - 1) * ((H.card - k : ℕ) : ℝ))) := by ring
      _ ≤ ((r + 1) / 2) * chore_maximin_share 2 u :=
        mul_le_mul_of_nonneg_left hlower halpha


private lemma in570_one_agent_balanced (m : ℕ) (r a : ℝ) (hr : 1 ≤ r) (ha : 0 < a)
    (u : Fin m → ℝ) (H S : Finset (Fin m))
    (hu : ∀ g, u g = if g ∈ H then r * a else a)
    (hs : S.card ≤ (m + 1) / 2)
    (hsc : (Finset.univ \ S).card ≤ (m + 1) / 2)
    (hh : (S ∩ H).card ≤ (H.card + 1) / 2)
    (hhc : (H \ S).card ≤ (H.card + 1) / 2) :
    additive_valuation u S ≤ ((r + 1) / 2) * chore_maximin_share 2 u ∧
    additive_valuation u (Finset.univ \ S) ≤
      ((r + 1) / 2) * chore_maximin_share 2 u := by
  have hupp := in570_balanced_upper_le_mms m r a hr ha u H hu
  refine ⟨le_trans (in570_balanced_cost_upper m r a hr ha u H S hu hs hh) hupp, ?_⟩
  have hint : ((Finset.univ \ S) ∩ H) = H \ S := by
    ext g
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  have hhh : ((Finset.univ \ S) ∩ H).card ≤ (H.card + 1) / 2 := by rw [hint]; exact hhc
  exact le_trans (in570_balanced_cost_upper m r a hr ha u H (Finset.univ \ S) hu hsc hhh) hupp


private lemma in570_swap_lottery (m : ℕ) (α : ℝ) (c : Fin 2 → Fin m → ℝ) (S : Finset (Fin m))
    (hS : ∀ i, additive_valuation (c i) S ≤ α * chore_maximin_share 2 (c i))
    (hSc : ∀ i, additive_valuation (c i) (Finset.univ \ S) ≤
      α * chore_maximin_share 2 (c i)) :
    ∃ p ∈ stdSimplex ℝ (Fin m → Fin 2),
      is_equal_marginal_lottery p ∧ is_ex_post_alpha_mms_chores α c p := by
  classical
  let σ : Fin m → Fin 2 := fun g => if g ∈ S then 0 else 1
  let τ : Fin m → Fin 2 := fun g => if g ∈ S then 1 else 0
  let p : (Fin m → Fin 2) → ℝ := fun t =>
    (if t = σ then 1 / 2 else 0) + (if t = τ then 1 / 2 else 0)
  have bσ0 : bundle_of σ 0 = S := by
    ext g
    simp [bundle_of, σ]
  have bσ1 : bundle_of σ 1 = Finset.univ \ S := by
    ext g
    simp [bundle_of, σ]
  have bτ0 : bundle_of τ 0 = Finset.univ \ S := by
    ext g
    simp [bundle_of, τ]
  have bτ1 : bundle_of τ 1 = S := by
    ext g
    simp [bundle_of, τ]
  refine ⟨p, ?_, ?_, ?_⟩
  · constructor
    · intro t
      dsimp [p]
      positivity
    · dsimp [p]
      rw [Finset.sum_add_distrib]
      simp <;> norm_num
  · intro g i
    change (∑ t : Fin m → Fin 2, if t g = i then p t else 0) = 1 / (2 : ℝ)
    have hστ : σ ≠ τ := by
      intro h
      have hv := congrFun h g
      by_cases hg : g ∈ S <;> simp [σ, τ, hg] at hv
    have hexpand (t : Fin m → Fin 2) :
        (if t g = i then p t else 0) =
          (if t = σ then (if σ g = i then (1 / 2 : ℝ) else 0) else 0) +
          (if t = τ then (if τ g = i then (1 / 2 : ℝ) else 0) else 0) := by
      by_cases hσ : t = σ
      · subst t
        simp [p, hστ]
      · by_cases hτ : t = τ
        · subst t
          simp [p, Ne.symm hστ]
        · simp [p, hσ, hτ]
    simp only [hexpand, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    fin_cases i <;> by_cases hg : g ∈ S <;> simp [σ, τ, hg]
  · intro t hp i
    change additive_valuation (c i) (bundle_of t i) ≤ α * chore_maximin_share 2 (c i)
    have ht : t = σ ∨ t = τ := by
      by_contra hh
      push_neg at hh
      simp [p, hh.1, hh.2] at hp
    rcases ht with rfl | rfl <;> fin_cases i
    · simpa [bσ0] using hS 0
    · simpa [bσ1] using hSc 1
    · simpa [bτ0] using hSc 0
    · simpa [bτ1] using hS 1

/-- Two-agent case: every scaled bivalued chore profile admits an equal-marginal ex-post ((r+1)/2)-MMS lottery. -/
theorem two_agent_bivalued_equal_marginal_sharp_mms
    (r : ℝ) (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (m : ℕ) (c : Fin 2 → Fin m → ℝ)
    (hc : is_scaled_bivalued_chores r c) :
    ∃ p ∈ stdSimplex ℝ (Fin m → Fin 2),
      is_equal_marginal_lottery p ∧
      is_ex_post_alpha_mms_chores ((r + 1) / 2) c p := by
  classical
  obtain ⟨a, ha, hv⟩ := hc
  let H : Fin 2 → Finset (Fin m) := fun i => Finset.univ.filter (fun g => c i g = r * a i)
  have hval (i : Fin 2) (g : Fin m) : c i g = if g ∈ H i then r * a i else a i := by
    by_cases h : c i g = r * a i
    · simp [H, h]
    · have hg := hv i g
      simp only [H, Finset.mem_filter, Finset.mem_univ, true_and, h, if_false]
      exact hg.resolve_right h
  obtain ⟨S, hs, hsc, h0, h0c, h1, h1c⟩ := in570_balance_two_subsets m (H 0) (H 1)
  have hboth (i : Fin 2) :
      additive_valuation (c i) S ≤ ((r + 1) / 2) * chore_maximin_share 2 (c i) ∧
      additive_valuation (c i) (Finset.univ \ S) ≤ ((r + 1) / 2) * chore_maximin_share 2 (c i) := by
    fin_cases i
    · exact in570_one_agent_balanced m r (a 0) hr1 (ha 0) (c 0) (H 0) S (hval 0) hs hsc h0 h0c
    · exact in570_one_agent_balanced m r (a 1) hr1 (ha 1) (c 1) (H 1) S (hval 1) hs hsc h1 h1c
  exact in570_swap_lottery m ((r + 1) / 2) c S (fun i => (hboth i).1) (fun i => (hboth i).2)
