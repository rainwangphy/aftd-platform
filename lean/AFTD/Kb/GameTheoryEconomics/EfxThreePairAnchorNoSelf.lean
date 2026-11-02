import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreePairAnchorValues
import AFTD.Kb.GameTheoryEconomics.EfxThreePairAnchorStart
import AFTD.Kb.GameTheoryEconomics.EfxAllsourceThreePairValues

/-!
# efx_three_pair_anchor_no_self

Topic: fair_division   Node: d8893adcca5b

Provenance: helper lemma. Common-anchor lift of the OP-7 all-source three-split barrier; experiment 11720 and an unproved anchor-count projection.

No owner self-champions the unallocated good in the anchor family.
-/

def efx_three_pair_anchor_no_self_anchor (r : ℕ) (i : Fin 4) (k : Fin r) : Fin (9+4*r) :=
  ⟨9 + (i:ℕ) + 4*(k:ℕ), by omega⟩
abbrev efx_three_pair_anchor_no_self_c (r : ℕ) : Fin (9+4*r) := Fin.castAdd (4*r) (8 : Fin 9)
def efx_three_pair_anchor_no_self_p0 (r : ℕ) (i : Fin 4) : Fin (9+4*r) := ⟨2*(i:ℕ), by omega⟩
def efx_three_pair_anchor_no_self_p1 (r : ℕ) (i : Fin 4) : Fin (9+4*r) := ⟨2*(i:ℕ)+1, by omega⟩
def efx_three_pair_anchor_no_self_anchors (r : ℕ) (i : Fin 4) : Finset (Fin (9+4*r)) :=
  Finset.univ.image (efx_three_pair_anchor_no_self_anchor r i)

theorem efx_three_pair_anchor_no_self_c_val (r : ℕ) :
    (efx_three_pair_anchor_no_self_c r : ℕ) = 8 := by
  simp [efx_three_pair_anchor_no_self_c, Fin.val_castAdd]

theorem efx_three_pair_anchor_no_self_anchor_val (r : ℕ) (i j : Fin 4) (k : Fin r) :
    efx_three_pair_anchor_values r j (efx_three_pair_anchor_no_self_anchor r i k) = 100 := by
  rw [efx_three_pair_anchor_values]
  rw [dif_neg]
  simp [efx_three_pair_anchor_no_self_anchor]
  omega

theorem efx_three_pair_anchor_no_self_anchor_start (r : ℕ) (i : Fin 4) (k : Fin r) :
    efx_three_pair_anchor_start r (efx_three_pair_anchor_no_self_anchor r i k) = i.castSucc := by
  rw [efx_three_pair_anchor_start]
  have hlt : ¬ ((efx_three_pair_anchor_no_self_anchor r i k : Fin (9+4*r)) : ℕ) < 9 := by
    simp [efx_three_pair_anchor_no_self_anchor]; omega
  rw [dif_neg hlt]
  apply Fin.ext
  simp only [Fin.val_castSucc, efx_three_pair_anchor_no_self_anchor]
  have h1 : 9 + (i:ℕ) + 4*(k:ℕ) - 9 = (i:ℕ) + 4*(k:ℕ) := by omega
  rw [h1, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt i.isLt

theorem efx_three_pair_anchor_no_self_filter_ge_eq (r : ℕ) (i : Fin 4) :
    (Finset.univ.filter (fun g : Fin (9+4*r) =>
        9 ≤ (g:ℕ) ∧ efx_three_pair_anchor_start r g = i.castSucc))
      = efx_three_pair_anchor_no_self_anchors r i := by
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, efx_three_pair_anchor_no_self_anchors, Finset.mem_image]
  constructor
  · intro ⟨h9, hs⟩
    refine ⟨⟨((g:ℕ) - 9)/4, ?_⟩, ?_⟩
    · have hlt : (g:ℕ) < 9 + 4*r := g.isLt
      have : (g:ℕ) - 9 < 4*r := by omega
      exact Nat.div_lt_of_lt_mul (by omega)
    · apply Fin.ext
      simp only [efx_three_pair_anchor_no_self_anchor]
      have hmod : ((g:ℕ) - 9) % 4 = (i:ℕ) := by
        rw [efx_three_pair_anchor_start] at hs
        have hlt : ¬ ((g:ℕ) < 9) := by omega
        rw [dif_neg hlt] at hs
        have := congrArg Fin.val hs
        simpa using this
      have hdm := Nat.div_add_mod ((g:ℕ) - 9) 4
      omega
  · rintro ⟨k, rfl⟩
    refine ⟨?_, efx_three_pair_anchor_no_self_anchor_start r i k⟩
    simp [efx_three_pair_anchor_no_self_anchor]
    omega

theorem efx_three_pair_anchor_no_self_anchors_card (r : ℕ) (i : Fin 4) :
    (efx_three_pair_anchor_no_self_anchors r i).card = r := by
  rw [efx_three_pair_anchor_no_self_anchors, Finset.card_image_of_injective]
  · simp
  · intro a b h
    have hv : 9 + (i:ℕ) + 4*(a:ℕ) = 9 + (i:ℕ) + 4*(b:ℕ) := by
      simpa [efx_three_pair_anchor_no_self_anchor] using congrArg Fin.val h
    apply Fin.ext
    omega

theorem efx_three_pair_anchor_no_self_anchors_sum (r : ℕ) (i j : Fin 4) :
    ∑ g ∈ efx_three_pair_anchor_no_self_anchors r i, efx_three_pair_anchor_values r j g = 100 * r := by
  rw [efx_three_pair_anchor_no_self_anchors, Finset.sum_image]
  · rw [Finset.sum_const_nat (fun k _ => efx_three_pair_anchor_no_self_anchor_val r i j k)]
    simp [Finset.card_univ, Nat.mul_comm]
  · intro a _ b _ h
    have hv : 9 + (i:ℕ) + 4*(a:ℕ) = 9 + (i:ℕ) + 4*(b:ℕ) := by
      simpa [efx_three_pair_anchor_no_self_anchor] using congrArg Fin.val h
    apply Fin.ext
    omega

theorem efx_three_pair_anchor_no_self_old_char (r : ℕ) (i : Fin 4) (g : Fin (9+4*r))
    (h : (g:ℕ) < 9) (hs : efx_three_pair_anchor_start r g = i.castSucc) :
    g = efx_three_pair_anchor_no_self_p0 r i ∨ g = efx_three_pair_anchor_no_self_p1 r i := by
  rw [efx_three_pair_anchor_start] at hs
  rw [dif_pos h] at hs
  have hv := congrArg Fin.val hs
  simp only [Fin.val_castSucc] at hv
  have hsplit : (g:ℕ) = 2*(i:ℕ) ∨ (g:ℕ) = 2*(i:ℕ) + 1 := by
    interval_cases (g:ℕ) <;> fin_cases i <;> simp_all
  rcases hsplit with h0 | h1
  · left; apply Fin.ext; simpa [efx_three_pair_anchor_no_self_p0] using h0
  · right; apply Fin.ext; simpa [efx_three_pair_anchor_no_self_p1] using h1

theorem efx_three_pair_anchor_no_self_mem_S_lt (r : ℕ) (i : Fin 4) (g : Fin (9+4*r))
    (hS : g ∈ insert (efx_three_pair_anchor_no_self_c r)
      (Finset.univ.filter (fun g => efx_three_pair_anchor_start r g = i.castSucc)))
    (h : (g:ℕ) < 9) :
    g = efx_three_pair_anchor_no_self_c r ∨ g = efx_three_pair_anchor_no_self_p0 r i ∨
      g = efx_three_pair_anchor_no_self_p1 r i := by
  rcases Finset.mem_insert.mp hS with rfl | hf
  · exact Or.inl rfl
  · right
    exact efx_three_pair_anchor_no_self_old_char r i g h (Finset.mem_filter.mp hf).2

theorem efx_three_pair_anchor_no_self_mem_S_ge (r : ℕ) (i : Fin 4) (g : Fin (9+4*r))
    (hS : g ∈ insert (efx_three_pair_anchor_no_self_c r)
      (Finset.univ.filter (fun g => efx_three_pair_anchor_start r g = i.castSucc)))
    (h : 9 ≤ (g:ℕ)) :
    g ∈ efx_three_pair_anchor_no_self_anchors r i := by
  rw [← efx_three_pair_anchor_no_self_filter_ge_eq]
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, h, ?_⟩
  rcases Finset.mem_insert.mp hS with rfl | hf
  · rw [efx_three_pair_anchor_no_self_c_val] at h
    omega
  · exact (Finset.mem_filter.mp hf).2

theorem efx_three_pair_anchor_no_self_p0p1_val (r : ℕ) (i : Fin 4) :
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_p0 r i) +
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_p1 r i) = 10 := by
  fin_cases i <;> simp [efx_three_pair_anchor_values, efx_allsource_three_pair_values,
    efx_three_pair_anchor_no_self_p0, efx_three_pair_anchor_no_self_p1]

theorem efx_three_pair_anchor_no_self_triple_le (r : ℕ) (i : Fin 4) :
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_c r) +
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_p0 r i) +
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_p1 r i) ≤ 15 := by
  fin_cases i <;> simp [efx_three_pair_anchor_values, efx_allsource_three_pair_values,
    efx_three_pair_anchor_no_self_c, efx_three_pair_anchor_no_self_p0, efx_three_pair_anchor_no_self_p1,
    Fin.val_castAdd]

theorem efx_three_pair_anchor_no_self_c_p0_le (r : ℕ) (i : Fin 4) :
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_c r) +
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_p0 r i) ≤ 10 := by
  fin_cases i <;> simp [efx_three_pair_anchor_values, efx_allsource_three_pair_values,
    efx_three_pair_anchor_no_self_c, efx_three_pair_anchor_no_self_p0, Fin.val_castAdd]

theorem efx_three_pair_anchor_no_self_c_p1_le (r : ℕ) (i : Fin 4) :
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_c r) +
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_p1 r i) ≤ 10 := by
  fin_cases i <;> simp [efx_three_pair_anchor_values, efx_allsource_three_pair_values,
    efx_three_pair_anchor_no_self_c, efx_three_pair_anchor_no_self_p1, Fin.val_castAdd]

theorem efx_three_pair_anchor_no_self_foreign_gt (r : ℕ) (i : Fin 4) :
    10 < efx_three_pair_anchor_values r (if i = 0 then 1 else 0) (efx_three_pair_anchor_no_self_c r) +
    efx_three_pair_anchor_values r (if i = 0 then 1 else 0) (efx_three_pair_anchor_no_self_p1 r i) := by
  fin_cases i <;> simp [efx_three_pair_anchor_values, efx_allsource_three_pair_values,
    efx_three_pair_anchor_no_self_c, efx_three_pair_anchor_no_self_p1, Fin.val_castAdd]

theorem efx_three_pair_anchor_no_self_triple_sum (r : ℕ) (i : Fin 4) :
    ∑ g ∈ ({efx_three_pair_anchor_no_self_c r, efx_three_pair_anchor_no_self_p0 r i,
      efx_three_pair_anchor_no_self_p1 r i} : Finset (Fin (9+4*r))),
      efx_three_pair_anchor_values r i g =
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_c r) +
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_p0 r i) +
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_p1 r i) := by
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · omega
  · simp [efx_three_pair_anchor_no_self_p0, efx_three_pair_anchor_no_self_p1, Fin.ext_iff]
  · simp [efx_three_pair_anchor_no_self_c, efx_three_pair_anchor_no_self_p0, efx_three_pair_anchor_no_self_p1,
      Fin.ext_iff, Fin.val_castAdd]
    omega

theorem efx_three_pair_anchor_no_self_pair_sum (r : ℕ) (i : Fin 4) :
    ∑ g ∈ ({efx_three_pair_anchor_no_self_p0 r i, efx_three_pair_anchor_no_self_p1 r i} : Finset (Fin (9+4*r))),
      efx_three_pair_anchor_values r i g =
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_p0 r i) +
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_p1 r i) := by
  rw [Finset.sum_insert, Finset.sum_singleton]
  · simp [efx_three_pair_anchor_no_self_p0, efx_three_pair_anchor_no_self_p1, Fin.ext_iff]

theorem efx_three_pair_anchor_no_self_pair_c_p1_sum (r : ℕ) (i : Fin 4) :
    ∑ g ∈ ({efx_three_pair_anchor_no_self_c r, efx_three_pair_anchor_no_self_p1 r i} : Finset (Fin (9+4*r))),
      efx_three_pair_anchor_values r i g =
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_c r) +
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_p1 r i) := by
  rw [Finset.sum_insert, Finset.sum_singleton]
  · simp [efx_three_pair_anchor_no_self_c, efx_three_pair_anchor_no_self_p1, Fin.ext_iff, Fin.val_castAdd]
    omega

theorem efx_three_pair_anchor_no_self_pair_c_p0_sum (r : ℕ) (i : Fin 4) :
    ∑ g ∈ ({efx_three_pair_anchor_no_self_c r, efx_three_pair_anchor_no_self_p0 r i} : Finset (Fin (9+4*r))),
      efx_three_pair_anchor_values r i g =
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_c r) +
    efx_three_pair_anchor_values r i (efx_three_pair_anchor_no_self_p0 r i) := by
  rw [Finset.sum_insert, Finset.sum_singleton]
  · simp [efx_three_pair_anchor_no_self_c, efx_three_pair_anchor_no_self_p0, Fin.ext_iff, Fin.val_castAdd]
    omega

theorem efx_three_pair_anchor_no_self (r : ℕ) (i : Fin 4) (T : Finset (Fin (9+4*r)))
  (hT : T ⊆ insert (Fin.castAdd (4*r) (8 : Fin 9)) (Finset.univ.filter (fun g => efx_three_pair_anchor_start r g = i.castSucc)))
  (hprefer : 100*r+10 < ∑ g ∈ T, efx_three_pair_anchor_values r i g) :
  ∃ (j : Fin 4) (g : Fin (9+4*r)), g ∈ T ∧ 100*r+10 < ∑ h ∈ T.erase g, efx_three_pair_anchor_values r j h := by
  set oldT : Finset (Fin (9+4*r)) := T.filter (fun g => (g:ℕ) < 9) with holdTdef
  set ancT : Finset (Fin (9+4*r)) := T.filter (fun g => 9 ≤ (g:ℕ)) with hancTdef
  have hsplit : (∑ g ∈ T, efx_three_pair_anchor_values r i g) =
      (∑ g ∈ oldT, efx_three_pair_anchor_values r i g) +
      (∑ g ∈ ancT, efx_three_pair_anchor_values r i g) := by
    rw [holdTdef, hancTdef]
    rw [← Finset.sum_filter_add_sum_filter_not T (fun g : Fin (9+4*r) => (g:ℕ) < 9)
      (fun g => efx_three_pair_anchor_values r i g)]
    congr 1
    exact Finset.sum_congr (Finset.filter_congr (by intro g _; omega)) (by intro x _; rfl)
  have holdT_sub : oldT ⊆ ({efx_three_pair_anchor_no_self_c r,
      efx_three_pair_anchor_no_self_p0 r i, efx_three_pair_anchor_no_self_p1 r i} :
      Finset (Fin (9+4*r))) := by
    intro g hg
    have hg' := hg
    rw [holdTdef, Finset.mem_filter] at hg'
    have hmem := efx_three_pair_anchor_no_self_mem_S_lt r i g (hT hg'.1) hg'.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    exact hmem
  have holdT_le : (∑ g ∈ oldT, efx_three_pair_anchor_values r i g) ≤ 15 := by
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun g => efx_three_pair_anchor_values r i g) holdT_sub (fun x _ _ => Nat.zero_le _)
    rw [efx_three_pair_anchor_no_self_triple_sum r i] at h1
    have h2 := efx_three_pair_anchor_no_self_triple_le r i
    omega
  have hancT_sub : ancT ⊆ efx_three_pair_anchor_no_self_anchors r i := by
    intro g hg
    rw [hancTdef, Finset.mem_filter] at hg
    exact efx_three_pair_anchor_no_self_mem_S_ge r i g (hT hg.1) hg.2
  have hancT_card_le : ancT.card ≤ r := by
    have := Finset.card_le_card hancT_sub
    rwa [efx_three_pair_anchor_no_self_anchors_card] at this
  have hancT_sum_eq : (∑ g ∈ ancT, efx_three_pair_anchor_values r i g) = ancT.card * 100 := by
    apply Finset.sum_const_nat
    intro g hg
    rw [hancTdef, Finset.mem_filter] at hg
    rw [efx_three_pair_anchor_values]
    rw [dif_neg]
    omega
  have hcard_ge : r ≤ ancT.card := by
    have h1 : 100*r + 10 < (∑ g ∈ oldT, efx_three_pair_anchor_values r i g) +
        (∑ g ∈ ancT, efx_three_pair_anchor_values r i g) := by
      rw [← hsplit]; exact hprefer
    rw [hancT_sum_eq] at h1
    by_contra hc
    have hc' : ancT.card + 1 ≤ r := by omega
    have h2 : ancT.card * 100 + 100 ≤ r * 100 := by omega
    omega
  have hcard_eq : ancT.card = r := le_antisymm hancT_card_le hcard_ge
  have hancT_eq : ancT = efx_three_pair_anchor_no_self_anchors r i :=
    Finset.eq_of_subset_of_card_le hancT_sub (by
      rw [efx_three_pair_anchor_no_self_anchors_card, hcard_eq])
  have hanchors_mem : ∀ k : Fin r, efx_three_pair_anchor_no_self_anchor r i k ∈ T := by
    intro k
    have h1 : efx_three_pair_anchor_no_self_anchor r i k ∈ ancT := by
      rw [hancT_eq]
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
    exact (Finset.mem_filter.mp h1).1
  have hancT_sum_100 : (∑ g ∈ ancT, efx_three_pair_anchor_values r i g) = 100*r := by
    rw [hancT_sum_eq, hcard_eq, Nat.mul_comm]
  have holdT_gt : 10 < ∑ g ∈ oldT, efx_three_pair_anchor_values r i g := by
    have h1 : 100*r + 10 < (∑ g ∈ oldT, efx_three_pair_anchor_values r i g) +
        (∑ g ∈ ancT, efx_three_pair_anchor_values r i g) := by
      rw [← hsplit]; exact hprefer
    rw [hancT_sum_100] at h1
    omega
  have hc_mem : efx_three_pair_anchor_no_self_c r ∈ T := by
    by_contra hc
    have hsub : oldT ⊆ ({efx_three_pair_anchor_no_self_p0 r i,
        efx_three_pair_anchor_no_self_p1 r i} : Finset (Fin (9+4*r))) := by
      intro g hg
      have hg' := hg
      rw [holdTdef, Finset.mem_filter] at hg'
      have hmem := holdT_sub hg
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
      rcases hmem with rfl | rfl | rfl
      · exact absurd hg'.1 hc
      · exact Or.inl rfl
      · exact Or.inr rfl
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun g => efx_three_pair_anchor_values r i g) hsub (fun x _ _ => Nat.zero_le _)
    rw [efx_three_pair_anchor_no_self_pair_sum r i,
        efx_three_pair_anchor_no_self_p0p1_val r i] at h1
    omega
  have hp0_mem : efx_three_pair_anchor_no_self_p0 r i ∈ T := by
    by_contra hp0
    have hsub : oldT ⊆ ({efx_three_pair_anchor_no_self_c r,
        efx_three_pair_anchor_no_self_p1 r i} : Finset (Fin (9+4*r))) := by
      intro g hg
      have hg' := hg
      rw [holdTdef, Finset.mem_filter] at hg'
      have hmem := holdT_sub hg
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
      rcases hmem with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd hg'.1 hp0
      · exact Or.inr rfl
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun g => efx_three_pair_anchor_values r i g) hsub (fun x _ _ => Nat.zero_le _)
    rw [efx_three_pair_anchor_no_self_pair_c_p1_sum r i] at h1
    have h2 := efx_three_pair_anchor_no_self_c_p1_le r i
    omega
  have hp1_mem : efx_three_pair_anchor_no_self_p1 r i ∈ T := by
    by_contra hp1
    have hsub : oldT ⊆ ({efx_three_pair_anchor_no_self_c r,
        efx_three_pair_anchor_no_self_p0 r i} : Finset (Fin (9+4*r))) := by
      intro g hg
      have hg' := hg
      rw [holdTdef, Finset.mem_filter] at hg'
      have hmem := holdT_sub hg
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
      rcases hmem with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hg'.1 hp1
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun g => efx_three_pair_anchor_values r i g) hsub (fun x _ _ => Nat.zero_le _)
    rw [efx_three_pair_anchor_no_self_pair_c_p0_sum r i] at h1
    have h2 := efx_three_pair_anchor_no_self_c_p0_le r i
    omega
  refine ⟨(if i = 0 then 1 else 0), efx_three_pair_anchor_no_self_p0 r i, hp0_mem, ?_⟩
  have hA_sub : (insert (efx_three_pair_anchor_no_self_c r)
      (insert (efx_three_pair_anchor_no_self_p1 r i)
        (efx_three_pair_anchor_no_self_anchors r i))) ⊆
      T.erase (efx_three_pair_anchor_no_self_p0 r i) := by
    intro x hx
    rw [Finset.mem_erase]
    constructor
    · intro hxg
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · have hv := congrArg Fin.val hxg
        rw [efx_three_pair_anchor_no_self_c_val] at hv
        simp only [efx_three_pair_anchor_no_self_p0] at hv
        omega
      · rcases Finset.mem_insert.mp hx' with rfl | hx''
        · have hv := congrArg Fin.val hxg
          simp only [efx_three_pair_anchor_no_self_p0, efx_three_pair_anchor_no_self_p1] at hv
          omega
        · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx''
          have hv := congrArg Fin.val hxg
          simp only [efx_three_pair_anchor_no_self_anchor, efx_three_pair_anchor_no_self_p0] at hv
          omega
    · rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact hc_mem
      · rcases Finset.mem_insert.mp hx' with rfl | hx''
        · exact hp1_mem
        · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx''
          exact hanchors_mem k
  have hp1_not_anchors : efx_three_pair_anchor_no_self_p1 r i ∉ efx_three_pair_anchor_no_self_anchors r i := by
    intro hmem
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hmem
    have hv := congrArg Fin.val hk
    simp only [efx_three_pair_anchor_no_self_anchor, efx_three_pair_anchor_no_self_p1] at hv
    omega
  have hc_not : efx_three_pair_anchor_no_self_c r ∉ insert (efx_three_pair_anchor_no_self_p1 r i)
        (efx_three_pair_anchor_no_self_anchors r i) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · have hv := congrArg Fin.val h
      simp only [efx_three_pair_anchor_no_self_c, efx_three_pair_anchor_no_self_p1, Fin.val_castAdd] at hv
      omega
    · obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
      have hv := congrArg Fin.val hk
      simp only [efx_three_pair_anchor_no_self_c, efx_three_pair_anchor_no_self_anchor, Fin.val_castAdd] at hv
      omega
  have hsum_le : (∑ x ∈ (insert (efx_three_pair_anchor_no_self_c r)
      (insert (efx_three_pair_anchor_no_self_p1 r i)
        (efx_three_pair_anchor_no_self_anchors r i))),
        efx_three_pair_anchor_values r (if i = 0 then 1 else 0) x) ≤
      ∑ x ∈ T.erase (efx_three_pair_anchor_no_self_p0 r i),
        efx_three_pair_anchor_values r (if i = 0 then 1 else 0) x :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun x => efx_three_pair_anchor_values r (if i = 0 then 1 else 0) x)
      hA_sub (fun _ _ _ => Nat.zero_le _)
  have hA_sum : (∑ x ∈ (insert (efx_three_pair_anchor_no_self_c r)
      (insert (efx_three_pair_anchor_no_self_p1 r i)
        (efx_three_pair_anchor_no_self_anchors r i))),
        efx_three_pair_anchor_values r (if i = 0 then 1 else 0) x) =
      efx_three_pair_anchor_values r (if i = 0 then 1 else 0) (efx_three_pair_anchor_no_self_c r) +
      efx_three_pair_anchor_values r (if i = 0 then 1 else 0) (efx_three_pair_anchor_no_self_p1 r i) + 100*r := by
    rw [Finset.sum_insert hc_not, Finset.sum_insert hp1_not_anchors,
      efx_three_pair_anchor_no_self_anchors_sum r i (if i = 0 then 1 else 0)]
    omega
  have hA_gt : 100*r+10 < (∑ x ∈ (insert (efx_three_pair_anchor_no_self_c r)
      (insert (efx_three_pair_anchor_no_self_p1 r i)
        (efx_three_pair_anchor_no_self_anchors r i))),
        efx_three_pair_anchor_values r (if i = 0 then 1 else 0) x) := by
    rw [hA_sum]
    have := efx_three_pair_anchor_no_self_foreign_gt r i
    omega
  exact lt_of_lt_of_le hA_gt hsum_le
