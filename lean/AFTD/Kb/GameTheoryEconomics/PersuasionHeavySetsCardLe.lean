import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionHalfWeightSumLe

/-!
# persuasion_heavy_sets_card_le

Topic: mechanism_design   Node: bf839219e985

Main counting lemma. For nonnegative weights w on Fin (2m+1) with positive total W, at most C(2m+1, m) - C(2m-1, m) of the m-subsets have weight at least W/2. Equality holds for the weights 1/2, 1/2 on two points.
-/

open Finset in
/-- The `m`-subsets of `Fin (2m+1)` disjoint from a fixed `m`-subset: there are `m + 1`. -/
lemma persuasion_disjoint_count (m : ℕ) (i : Finset (Fin (2 * m + 1))) (hi : i.card = m) :
    ((powersetCard m (Finset.univ : Finset (Fin (2 * m + 1)))).filter (fun i' => Disjoint i i')).card
      = m + 1 := by
  have h : (powersetCard m (Finset.univ : Finset (Fin (2 * m + 1)))).filter (fun i' => Disjoint i i')
      = powersetCard m iᶜ := by
    ext i'
    simp only [Finset.mem_filter, mem_powersetCard, Finset.subset_univ, true_and]
    rw [Finset.subset_compl_iff_disjoint_left]
    tauto
  rw [h, card_powersetCard, Finset.card_compl, Fintype.card_fin, hi,
    show 2 * m + 1 - m = m + 1 by omega, Nat.choose_succ_self_right]

open Finset in
/-- **Main counting lemma.** For nonnegative weights `w` on `Fin (2m+1)` with positive total
`W`, at most `C(2m+1, m) - C(2m-1, m)` of the `m`-subsets have weight at least `W/2`. Equality
holds for the weights `1/2, 1/2` on two points. -/
lemma persuasion_heavy_sets_card_le (m : ℕ) (hm : 1 ≤ m) (w : Fin (2 * m + 1) → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hW : 0 < ∑ j, w j) :
    ((powersetCard m (Finset.univ : Finset (Fin (2 * m + 1)))).filter
        (fun i => ∑ j, w j ≤ 2 * ∑ j ∈ i, w j)).card + (2 * m - 1).choose m
      ≤ (2 * m + 1).choose m := by
  classical
  set W := ∑ j, w j with hWdef
  set 𝓜 := powersetCard m (Finset.univ : Finset (Fin (2 * m + 1))) with h𝓜
  set G := 𝓜.filter (fun i => W ≤ 2 * ∑ j ∈ i, w j) with hG
  set Prs := (𝓜 ×ˢ 𝓜).filter (fun p => Disjoint p.1 p.2) with hPrs
  set Tie := Prs.filter (fun p => 2 * ∑ j ∈ p.1, w j = W ∧ 2 * ∑ j ∈ p.2, w j = W) with hTie
  let gd : Finset (Fin (2 * m + 1)) → ℕ := fun i => if W ≤ 2 * ∑ j ∈ i, w j then 1 else 0
  -- sums over Prs as iterated sums
  have hPrssum : ∀ f : Finset (Fin (2 * m + 1)) × Finset (Fin (2 * m + 1)) → ℕ,
      ∑ p ∈ Prs, f p = ∑ i ∈ 𝓜, ∑ i' ∈ 𝓜.filter (fun i' => Disjoint i i'), f (i, i') := by
    intro f
    rw [hPrs, sum_filter, sum_product]
    apply sum_congr rfl
    intro i _
    rw [sum_filter]
  have hdc : ∀ i ∈ 𝓜, (𝓜.filter (fun i' => Disjoint i i')).card = m + 1 :=
    fun i hi => persuasion_disjoint_count m i (mem_powersetCard.mp hi).2
  have hgdG : ∑ i ∈ 𝓜, gd i = G.card := by
    rw [hG, card_filter]
  -- (1) the double count
  have h1 : ∑ p ∈ Prs, (gd p.1 + gd p.2) = 2 * ((m + 1) * G.card) := by
    rw [sum_add_distrib, hPrssum, hPrssum]
    have a1 : ∑ i ∈ 𝓜, ∑ i' ∈ 𝓜.filter (fun i' => Disjoint i i'), gd (i, i').1
        = (m + 1) * G.card := by
      simp only
      rw [← hgdG, mul_sum]
      apply sum_congr rfl
      intro i hi
      rw [Finset.sum_const, hdc i hi, smul_eq_mul]
    have a2 : ∑ i ∈ 𝓜, ∑ i' ∈ 𝓜.filter (fun i' => Disjoint i i'), gd (i, i').2
        = (m + 1) * G.card := by
      simp only
      have : ∑ i ∈ 𝓜, ∑ i' ∈ 𝓜.filter (fun i' => Disjoint i i'), gd i'
          = ∑ i' ∈ 𝓜, ∑ i ∈ 𝓜.filter (fun i => Disjoint i' i), gd i' := by
        simp_rw [sum_filter]
        rw [sum_comm]
        apply sum_congr rfl; intro i' _; apply sum_congr rfl; intro i _
        simp [disjoint_comm]
      rw [this, ← hgdG, mul_sum]
      apply sum_congr rfl
      intro i hi
      rw [Finset.sum_const, hdc i hi, smul_eq_mul]
    rw [a1, a2]; ring
  -- (2) pointwise bound
  have h2 : ∀ p ∈ Prs, gd p.1 + gd p.2 ≤ 1 + (if 2 * ∑ j ∈ p.1, w j = W ∧
      2 * ∑ j ∈ p.2, w j = W then 1 else 0) := by
    intro p hp
    rw [hPrs, Finset.mem_filter] at hp
    have hdisj := hp.2
    have hsum : ∑ j ∈ p.1, w j + ∑ j ∈ p.2, w j ≤ W := by
      rw [← sum_union hdisj, hWdef]
      exact sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hw j)
    have key : (W ≤ 2 * ∑ j ∈ p.1, w j) → (W ≤ 2 * ∑ j ∈ p.2, w j) →
        (2 * ∑ j ∈ p.1, w j = W ∧ 2 * ∑ j ∈ p.2, w j = W) :=
      fun a b => ⟨by linarith, by linarith⟩
    simp only [gd]
    split_ifs <;> (try omega) <;> exact absurd (key (by assumption) (by assumption)) (by assumption)
  -- (3) ties
  have h3 : Tie.card ≤ m * (2 * m).choose m := by
    let Z := Finset.univ.filter (fun e : Fin (2 * m + 1) => w e = 0)
    let S : Fin (2 * m + 1) → Finset (Finset (Fin (2 * m + 1))) := fun e =>
      (powersetCard m (Finset.univ.erase e)).filter (fun i => 2 * ∑ j ∈ i, w j = W)
    have hsub : Tie ⊆ Z.biUnion (fun e => (S e).image (fun i => (i, (insert e i)ᶜ))) := by
      intro p hp
      rw [hTie, hPrs, Finset.mem_filter, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨⟨hp1, hp2⟩, hdisj⟩, hw1, hw2⟩ := hp
      rw [h𝓜, mem_powersetCard] at hp1 hp2
      have hcu : (p.1 ∪ p.2).card = 2 * m := by
        rw [card_union_of_disjoint hdisj, hp1.2, hp2.2]; ring
      have hcc : (p.1 ∪ p.2)ᶜ.card = 1 := by
        rw [Finset.card_compl, Fintype.card_fin, hcu]; omega
      obtain ⟨e, he⟩ := card_eq_one.mp hcc
      have hmem : ∀ x, x ∉ p.1 ∪ p.2 ↔ x = e := by
        intro x
        rw [← Finset.mem_compl, he, Finset.mem_singleton]
      have hWe : W = ∑ j ∈ p.1, w j + ∑ j ∈ p.2, w j + w e := by
        rw [hWdef, ← sum_add_sum_compl (p.1 ∪ p.2), sum_union hdisj, he, sum_singleton]
      have hwe : w e = 0 := by linarith
      have he1 : e ∉ p.1 := fun h => (hmem e).mpr rfl (Finset.mem_union_left _ h)
      rw [Finset.mem_biUnion]
      refine ⟨e, by simp [Z, hwe], ?_⟩
      rw [Finset.mem_image]
      refine ⟨p.1, ?_, ?_⟩
      · rw [Finset.mem_filter, mem_powersetCard]
        refine ⟨⟨fun x hx => mem_erase.mpr ⟨fun h => he1 (h ▸ hx), Finset.mem_univ x⟩, hp1.2⟩, hw1⟩
      · ext1
        · rfl
        · ext x
          simp only [Finset.mem_compl, Finset.mem_insert, not_or]
          constructor
          · rintro ⟨hxe, hx1⟩
            by_contra hx2
            exact hxe ((hmem x).mp (by simp [hx1, hx2]))
          · intro hx2
            refine ⟨fun h => (hmem x).mpr h (Finset.mem_union_right _ hx2), ?_⟩
            exact Finset.disjoint_right.mp hdisj hx2
    calc Tie.card ≤ (Z.biUnion (fun e => (S e).image (fun i => (i, (insert e i)ᶜ)))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ e ∈ Z, ((S e).image (fun i => (i, (insert e i)ᶜ))).card := Finset.card_biUnion_le
      _ ≤ ∑ e ∈ Z, (S e).card := sum_le_sum (fun e _ => card_image_le)
      _ ≤ m * (2 * m).choose m := persuasion_half_weight_sum_le m hm w hw hW
  -- (4) number of disjoint pairs
  have h4 : Prs.card = (m + 1) * (2 * m + 1).choose m := by
    rw [card_eq_sum_ones, hPrssum]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    rw [sum_congr rfl (fun i hi => hdc i hi), Finset.sum_const, smul_eq_mul, h𝓜, card_powersetCard,
      card_univ, Fintype.card_fin]
    ring
  have hmain : 2 * ((m + 1) * G.card) ≤ (m + 1) * (2 * m + 1).choose m + m * (2 * m).choose m := by
    rw [← h1, ← h4]
    calc ∑ p ∈ Prs, (gd p.1 + gd p.2)
        ≤ ∑ p ∈ Prs, (1 + (if 2 * ∑ j ∈ p.1, w j = W ∧ 2 * ∑ j ∈ p.2, w j = W then 1 else 0)) :=
          sum_le_sum h2
      _ = Prs.card + Tie.card := by
          rw [sum_add_distrib, card_eq_sum_ones, hTie, card_filter]
      _ ≤ Prs.card + m * (2 * m).choose m := Nat.add_le_add_left h3 _
  -- arithmetic
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have c1 : (2 * (k + 1)).choose (k + 1) = 2 * (2 * (k + 1) - 1).choose (k + 1) := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.choose_succ_succ,
      show 2 * k + 1 + 1 - 1 = 2 * k + 1 by omega]
    have : (2 * k + 1).choose k = (2 * k + 1).choose (k + 1) := by
      rw [← Nat.choose_symm (by omega : k ≤ 2 * k + 1)]; congr 1; omega
    rw [this]; ring
  have c2 : (k + 1 + 1) * (2 * (k + 1) + 1).choose (k + 1)
      = (2 * (k + 1) + 1) * (2 * (k + 1)).choose (k + 1) := by
    have h := Nat.add_one_mul_choose_eq (2 * (k + 1)) (k + 1)
    have hs : (2 * (k + 1) + 1).choose (k + 1 + 1) = (2 * (k + 1) + 1).choose (k + 1) := by
      rw [← Nat.choose_symm (by omega : k + 1 + 1 ≤ 2 * (k + 1) + 1)]; congr 1; omega
    rw [hs] at h
    linarith
  set c := (2 * (k + 1) - 1).choose (k + 1)
  rw [c1] at hmain c2
  have : (k + 1 + 1) * (G.card + c) ≤ (k + 1 + 1) * (2 * (k + 1) + 1).choose (k + 1) := by
    nlinarith
  exact Nat.le_of_mul_le_mul_left this (by omega)
