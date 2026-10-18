import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopyColourInjective
import AFTD.Kb.Tcs.HasMonochromaticFanCopyColourInjective
import AFTD.Kb.Tcs.HasMonochromaticFanCopy
import AFTD.Kb.Tcs.MixedRamseyProperty
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopy

/-!
# mixed_diamond_fan_ramsey_bound_singleton_diamond_step

Topic: combinatorics   Node: 544423830535

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound

Case b ≥ 1 with a singleton {x} whose colour is the diamond colour c: if d ≥ j*a + (j-1)*b + 1 and the statement holds at (a-1, b+1) in dimension d-1, then χ already has a monochromatic diamond in one of the a diamond colours or a monochromatic F_j in one of the b fan colours.
-/

open Finset

def mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val (a b : ℕ) (c_val : ℕ) (v : ℕ) : ℕ :=
  if v < a - 1 then
    if v < c_val then v else v + 1
  else
    if v - (a - 1) < b then a + (v - (a - 1))
    else c_val

def mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_val (a b : ℕ) (c_val : ℕ) (v : ℕ) : ℕ :=
  if v < a then
    if v < c_val then v
    else if v = c_val then (a - 1) + b
    else v - 1
  else (a - 1) + (v - a)

lemma mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val_lt (a b : ℕ) (c_val : ℕ) (v : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : c_val < a) (hv : v < (a - 1) + (b + 1)) :
    mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val a b c_val v < a + b := by
  dsimp [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val]
  split_ifs <;> omega

lemma mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_val_lt (a b : ℕ) (c_val : ℕ) (v : ℕ)
    (ha : 1 ≤ a) (_hb : 1 ≤ b) (_hc : c_val < a) (hv : v < a + b) :
    mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_val a b c_val v < (a - 1) + (b + 1) := by
  dsimp [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_val]
  split_ifs <;> omega

def mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (c : Fin a) (i : Fin ((a - 1) + (b + 1))) : Fin (a + b) :=
  ⟨mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val a b c.val i.val,
   mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val_lt a b c.val i.val ha hb c.isLt i.isLt⟩

def mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_col (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (c : Fin a) (i : Fin (a + b)) : Fin ((a - 1) + (b + 1)) :=
  ⟨mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_val a b c.val i.val,
   mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_val_lt a b c.val i.val ha hb c.isLt i.isLt⟩

lemma mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_g_col (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (c : Fin a) (i : Fin (a + b)) :
    mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col a b ha hb c
      (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_col a b ha hb c i) = i := by
  ext
  dsimp [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col,
    mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_col,
    mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val,
    mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_val]
  split_ifs <;> omega

lemma mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_f_col (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (c : Fin a) (i : Fin ((a - 1) + (b + 1))) :
    mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_col a b ha hb c
      (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col a b ha hb c i) = i := by
  ext
  dsimp [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col,
    mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_col,
    mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val,
    mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_val]
  split_ifs <;> omega

lemma mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col_inj (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (c : Fin a) :
    Function.Injective (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col a b ha hb c) := by
  intro y1 y2 h
  have h1 := congrArg (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_col a b ha hb c) h
  rw [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_f_col,
      mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_f_col] at h1
  exact h1

lemma mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col_diamond (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (c : Fin a) (col : Fin (a - 1)) :
    ∃ col' : Fin a, mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col a b ha hb c
      (Fin.castAdd (b + 1) col) = Fin.castAdd b col' := by
  have hv : mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val a b c.val (Fin.castAdd (b + 1) col).val < a := by
    dsimp [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val]
    split_ifs <;> omega
  refine ⟨⟨mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val a b c.val (Fin.castAdd (b + 1) col).val, hv⟩, ?_⟩
  ext
  rfl

lemma mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col_fan (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (c : Fin a) (col : Fin (b + 1)) :
    (∃ col' : Fin b, mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col a b ha hb c
      (Fin.natAdd (a - 1) col) = Fin.natAdd a col') ∨
    (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col a b ha hb c
      (Fin.natAdd (a - 1) col) = Fin.castAdd b c) := by
  by_cases hcol : col.val < b
  · left
    have hv : a ≤ mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val a b c.val (Fin.natAdd (a - 1) col).val := by
      dsimp [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val]
      split_ifs <;> omega
    have hv2 : mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val a b c.val (Fin.natAdd (a - 1) col).val - a < b := by
      dsimp [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val]
      split_ifs <;> omega
    refine ⟨⟨mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val a b c.val (Fin.natAdd (a - 1) col).val - a, hv2⟩, ?_⟩
    ext
    dsimp [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col,
      mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val]
    split_ifs <;> omega
  · right
    ext
    dsimp [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col,
      mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_val]
    split_ifs <;> omega

def mixed_diamond_fan_ramsey_bound_singleton_diamond_step_emb (d : ℕ) (hd : 1 ≤ d) (x : Fin d) : Fin (d - 1) ↪ Fin d :=
  let hd' : d - 1 + 1 = d := Nat.sub_add_cancel hd
  let e : Fin d ≃ Fin (d - 1 + 1) := (Fin.castOrderIso hd'.symm).toEquiv
  let x' : Fin (d - 1 + 1) := e x
  { toFun := fun i => e.symm (x'.succAbove i)
    inj' := fun _ _ h => by
      have h1 := e.symm.injective h
      exact Fin.succAbove_right_injective h1 }

lemma mixed_diamond_fan_ramsey_bound_singleton_diamond_step_emb_ne (d : ℕ) (hd : 1 ≤ d) (x : Fin d) (i : Fin (d - 1)) :
    mixed_diamond_fan_ramsey_bound_singleton_diamond_step_emb d hd x i ≠ x := by
  have hd' : d - 1 + 1 = d := Nat.sub_add_cancel hd
  let e : Fin d ≃ Fin (d - 1 + 1) := (Fin.castOrderIso hd'.symm).toEquiv
  let x' : Fin (d - 1 + 1) := e x
  intro h
  have h1 : e (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_emb d hd x i) = e x := congrArg e h
  have h2 : e (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_emb d hd x i) = x'.succAbove i := by
    change e (e.symm (x'.succAbove i)) = _
    rw [Equiv.apply_symm_apply]
  rw [h2] at h1
  exact Fin.succAbove_ne x' i h1

def mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S (d : ℕ) (hd : 1 ≤ d) (x : Fin d)
    (B : Finset (Fin (d - 1))) : Finset (Fin d) :=
  B.map (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_emb d hd x) ∪ {x}

lemma mixed_diamond_fan_ramsey_bound_singleton_diamond_step_subset_iff_S_subset_S {d : ℕ} (hd : 1 ≤ d) (x : Fin d)
    (B B' : Finset (Fin (d - 1))) :
    mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x B ⊆
      mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x B' ↔ B ⊆ B' := by
  constructor
  · intro h y hy
    have hymem : mixed_diamond_fan_ramsey_bound_singleton_diamond_step_emb d hd x y ∈
        mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x B := by
      simp [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S, hy]
    have hx' := h hymem
    simp only [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S, mem_union, mem_map, mem_singleton] at hx'
    rcases hx' with ⟨z, hz, hz'⟩ | hzx
    · exact (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_emb d hd x).injective hz' ▸ hz
    · exact False.elim (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_emb_ne d hd x y hzx)
  · intro h
    simp only [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S, union_subset_iff]
    constructor
    · intro z hz
      simp only [mem_map] at hz
      rcases hz with ⟨w, hw, rfl⟩
      simp only [mem_union, mem_map]
      left
      exact ⟨w, h hw, rfl⟩
    · simp

lemma mixed_diamond_fan_ramsey_bound_singleton_diamond_step_ssubset_iff_S_ssubset_S {d : ℕ} (hd : 1 ≤ d) (x : Fin d)
    (B B' : Finset (Fin (d - 1))) :
    mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x B ⊂
      mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x B' ↔ B ⊂ B' := by
  change (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x B ⊆
            mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x B' ∧
          ¬ mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x B' ⊆
            mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x B) ↔ (B ⊆ B' ∧ ¬ B' ⊆ B)
  rw [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_subset_iff_S_subset_S,
      mixed_diamond_fan_ramsey_bound_singleton_diamond_step_subset_iff_S_subset_S]

lemma mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S_empty {d : ℕ} (hd : 1 ≤ d) (x : Fin d) :
    mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x ∅ = {x} := by
  simp [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S]

lemma mixed_diamond_fan_ramsey_bound_singleton_diamond_step_fin_ne_of_two_le {j : ℕ} (hj : 2 ≤ j) (i : Fin j) :
    ∃ i' : Fin j, i' ≠ i := by
  by_cases hi : i.val = 0
  · refine ⟨⟨1, hj⟩, ?_⟩
    intro h
    have hval := congrArg Fin.val h
    dsimp at hval
    omega
  · refine ⟨⟨0, by omega⟩, ?_⟩
    intro h
    have hval := congrArg Fin.val h
    dsimp at hval
    omega

lemma mixed_diamond_fan_ramsey_bound_singleton_diamond_step_diamond_transfer {j d k : ℕ} (hd : 1 ≤ d) (x : Fin d)
    (col : Fin k) (χ : Finset (Fin d) → Fin k)
    (h : has_monochromatic_diamond_copy j (d - 1) col
      (fun B => χ (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x B))) :
    has_monochromatic_diamond_copy j d col χ := by
  rcases h with ⟨bot, top, hbot_top, hbot, htop, mid, hmid, hpair⟩
  refine ⟨mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x bot,
          mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x top, ?_, hbot, htop,
          fun i => mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x (mid i), ?_, ?_⟩
  · rw [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_ssubset_iff_S_ssubset_S]; exact hbot_top
  · intro i
    refine ⟨?_, ?_, (hmid i).2.2⟩
    · rw [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_ssubset_iff_S_ssubset_S]; exact (hmid i).1
    · rw [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_ssubset_iff_S_ssubset_S]; exact (hmid i).2.1
  · intro i i' hne
    rw [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_subset_iff_S_subset_S]
    exact hpair i i' hne

lemma mixed_diamond_fan_ramsey_bound_singleton_diamond_step_fan_transfer {j d k : ℕ} (hd : 1 ≤ d) (x : Fin d)
    (col : Fin k) (χ : Finset (Fin d) → Fin k)
    (h : has_monochromatic_fan_copy j (d - 1) col
      (fun B => χ (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x B))) :
    has_monochromatic_fan_copy j d col χ := by
  rcases h with ⟨top, htop, mid, hmid, hpair⟩
  refine ⟨mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x top, htop,
          fun i => mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x (mid i), ?_, ?_⟩
  · intro i
    refine ⟨?_, (hmid i).2⟩
    rw [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_ssubset_iff_S_ssubset_S]; exact (hmid i).1
  · intro i i' hne
    rw [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_subset_iff_S_subset_S]
    exact hpair i i' hne

lemma mixed_diamond_fan_ramsey_bound_singleton_diamond_step_fan_to_diamond_transfer {j d k : ℕ}
    (hj : 2 ≤ j) (hd : 1 ≤ d) (x : Fin d) (col : Fin k)
    (χ : Finset (Fin d) → Fin k)
    (hx : χ {x} = col)
    (h : has_monochromatic_fan_copy j (d - 1) col
      (fun B => χ (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x B))) :
    has_monochromatic_diamond_copy j d col χ := by
  rcases h with ⟨top, htop, mid, hmid, hpair⟩
  have hmid_ne_empty (i : Fin j) : mid i ≠ ∅ := by
    intro hempty
    rcases mixed_diamond_fan_ramsey_bound_singleton_diamond_step_fin_ne_of_two_le hj i with ⟨i', hne⟩
    have hsub : mid i ⊆ mid i' := hempty.symm ▸ empty_subset (mid i')
    exact hpair i i' (Ne.symm hne) hsub
  have hbot_mid (i : Fin j) : ∅ ⊂ mid i :=
    Finset.ssubset_iff_subset_ne.mpr ⟨empty_subset (mid i), Ne.symm (hmid_ne_empty i)⟩
  have hbot_top : ∅ ⊂ top := ssubset_trans (hbot_mid ⟨0, by omega⟩) (hmid ⟨0, by omega⟩).1
  have hS_empty : mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x ∅ = {x} :=
    mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S_empty hd x
  refine ⟨{x}, mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x top, ?_, hx, htop,
          fun i => mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd x (mid i), ?_, ?_⟩
  · rw [← hS_empty, mixed_diamond_fan_ramsey_bound_singleton_diamond_step_ssubset_iff_S_ssubset_S]
    exact hbot_top
  · intro i
    refine ⟨?_, ?_, (hmid i).2⟩
    · rw [← hS_empty, mixed_diamond_fan_ramsey_bound_singleton_diamond_step_ssubset_iff_S_ssubset_S]
      exact hbot_mid i
    · rw [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_ssubset_iff_S_ssubset_S]
      exact (hmid i).1
  · intro i i' hne
    rw [mixed_diamond_fan_ramsey_bound_singleton_diamond_step_subset_iff_S_subset_S]
    exact hpair i i' hne

/-- b ≥ 1 step with a diamond-coloured singleton {x}: colour A by χ(A ∪ {x}) on the other d-1 points and apply the (a-1, b+1) instance; the colour of {x} becomes the extra fan colour. -/
theorem mixed_diamond_fan_ramsey_bound_singleton_diamond_step (j a b d : ℕ) (hj : 2 ≤ j)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : j * a + (j - 1) * b + 1 ≤ d)
    (ih : mixed_ramsey_property j (a - 1) (b + 1) (d - 1))
    (χ : Finset (Fin d) → Fin (a + b)) (x : Fin d) (c : Fin a) (hx : χ {x} = Fin.castAdd b c) :
    (∃ col : Fin a, has_monochromatic_diamond_copy j d (Fin.castAdd b col) χ) ∨
      ∃ col : Fin b, has_monochromatic_fan_copy j d (Fin.natAdd a col) χ := by
  have hd_ge_1 : 1 ≤ d := by omega
  let χ' : Finset (Fin (d - 1)) → Fin (a + b) :=
    fun B => χ (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_S d hd_ge_1 x B)
  let ψ : Finset (Fin (d - 1)) → Fin ((a - 1) + (b + 1)) :=
    fun B => mixed_diamond_fan_ramsey_bound_singleton_diamond_step_g_col a b ha hb c (χ' B)
  have hχ'ψ : ∀ B, χ' B = mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col a b ha hb c (ψ B) :=
    fun B => (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_g_col a b ha hb c (χ' B)).symm
  rcases ih ψ with ⟨col, hcol⟩ | ⟨col, hcol⟩
  · left
    have hχ' : has_monochromatic_diamond_copy j (d - 1)
        (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col a b ha hb c (Fin.castAdd (b + 1) col)) χ' := by
      refine (has_monochromatic_diamond_copy_colour_injective
        (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col a b ha hb c)
        (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col_inj a b ha hb c)
        (Fin.castAdd (b + 1) col) ψ χ' hχ'ψ).mpr hcol
    rcases mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col_diamond a b ha hb c col with ⟨col', hcol'⟩
    rw [hcol'] at hχ'
    refine ⟨col', mixed_diamond_fan_ramsey_bound_singleton_diamond_step_diamond_transfer hd_ge_1 x (Fin.castAdd b col') χ hχ'⟩
  · have hχ' : has_monochromatic_fan_copy j (d - 1)
        (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col a b ha hb c (Fin.natAdd (a - 1) col)) χ' := by
      refine (has_monochromatic_fan_copy_colour_injective
        (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col a b ha hb c)
        (mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col_inj a b ha hb c)
        (Fin.natAdd (a - 1) col) ψ χ' hχ'ψ).mpr hcol
    rcases mixed_diamond_fan_ramsey_bound_singleton_diamond_step_f_col_fan a b ha hb c col with ⟨col', hcol'⟩ | hc_eq
    · right
      rw [hcol'] at hχ'
      refine ⟨col', mixed_diamond_fan_ramsey_bound_singleton_diamond_step_fan_transfer hd_ge_1 x (Fin.natAdd a col') χ hχ'⟩
    · left
      rw [hc_eq] at hχ'
      refine ⟨c, mixed_diamond_fan_ramsey_bound_singleton_diamond_step_fan_to_diamond_transfer
        hj hd_ge_1 x (Fin.castAdd b c) χ hx hχ'⟩
