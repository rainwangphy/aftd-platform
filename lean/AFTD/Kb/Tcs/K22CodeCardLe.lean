import AFTD.Prelude
import AFTD.Kb.Tcs.IsKstCode
import AFTD.Kb.Tcs.CardSimpleGraph

/-!
# k22_code_card_le

Topic: combinatorics   Node: b958490aac34

Provenance: formalization of a published result. Source: arXiv:2301.13305, Proposition 1.5; arXiv:2610.35136, Proposition 3.1

Let n be a natural number with 4 ≤ n. For every K_{2,2}-code C of simple graphs on Fin n, (n - 2) * Set.ncard C ≤ 2 ^ (n.choose 2).
-/

lemma k22_code_card_le_H_symmDiff {n : ℕ} (hn : 4 ≤ n) :
    let u : Fin n := ⟨0, by omega⟩
    let v : Fin n := ⟨1, by omega⟩
    let r : Fin n := ⟨2, by omega⟩
    let A : Finset (Fin n) := {u, v}
    let R : Finset (Fin n) := Finset.univ \ A
    let H : Fin n → SimpleGraph (Fin n) := fun y =>
      if y = r then ⊥ else SimpleGraph.between (A : Set (Fin n)) (↑({r, y} : Finset (Fin n))) ⊤
    ∀ ⦃y z : Fin n⦄, y ∈ R → z ∈ R → y ≠ z →
      symmDiff (H y) (H z) = SimpleGraph.between (A : Set (Fin n)) (↑({y, z} : Finset (Fin n))) ⊤ := by
  intro u v r A R H y z hy hz hyz
  have hyA : y ∉ A := (Finset.mem_sdiff.mp hy).2
  have hzA : z ∉ A := (Finset.mem_sdiff.mp hz).2
  have hrA : r ∉ A := by
    intro h
    have : r = u ∨ r = v := by simpa [A] using h
    rcases this with h1 | h2
    · have := Fin.mk.inj h1; contradiction
    · have := Fin.mk.inj h2; contradiction
  if hyr : y = r then
    subst hyr
    have hzr : z ≠ r := hyz.symm
    have hHr : H r = ⊥ := if_pos rfl
    have hHz : H z = SimpleGraph.between (A : Set (Fin n)) (↑({r, z} : Finset (Fin n))) ⊤ := if_neg hzr
    rw [hHr, hHz, bot_symmDiff]
  else
    if hzr : z = r then
      subst hzr
      have hHr : H r = ⊥ := if_pos rfl
      have hHy : H y = SimpleGraph.between (A : Set (Fin n)) (↑({r, y} : Finset (Fin n))) ⊤ := if_neg hyr
      rw [hHr, hHy, symmDiff_bot]
      congr 1
      ext a
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
      tauto
    else
      have hHy : H y = SimpleGraph.between (A : Set (Fin n)) (↑({r, y} : Finset (Fin n))) ⊤ := if_neg hyr
      have hHz : H z = SimpleGraph.between (A : Set (Fin n)) (↑({r, z} : Finset (Fin n))) ⊤ := if_neg hzr
      have hyr' : r ≠ y := Ne.symm hyr
      have hzr' : r ≠ z := Ne.symm hzr
      rw [hHy, hHz]
      ext a b
      change (SimpleGraph.between (A : Set (Fin n)) (↑({r, y} : Finset (Fin n))) ⊤).Adj a b ∧ ¬ (SimpleGraph.between (A : Set (Fin n)) (↑({r, z} : Finset (Fin n))) ⊤).Adj a b ∨
        (SimpleGraph.between (A : Set (Fin n)) (↑({r, z} : Finset (Fin n))) ⊤).Adj a b ∧ ¬ (SimpleGraph.between (A : Set (Fin n)) (↑({r, y} : Finset (Fin n))) ⊤).Adj a b ↔
        (SimpleGraph.between (A : Set (Fin n)) (↑({y, z} : Finset (Fin n))) ⊤).Adj a b
      simp only [SimpleGraph.between_adj, SimpleGraph.top_adj, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
      by_cases ha : a ∈ A <;> by_cases hb : b ∈ A
      · have h1 : a ≠ r := fun h => hrA (h ▸ ha)
        have h2 : a ≠ y := fun h => hyA (h ▸ ha)
        have h3 : a ≠ z := fun h => hzA (h ▸ ha)
        have h4 : b ≠ r := fun h => hrA (h ▸ hb)
        have h5 : b ≠ y := fun h => hyA (h ▸ hb)
        have h6 : b ≠ z := fun h => hzA (h ▸ hb)
        simp [ha, hb, h1, h2, h3, h4, h5, h6]
      · have hab : a ≠ b := fun h => hb (h ▸ ha)
        rcases eq_or_ne b r with rfl | hbr
        · simp [ha, hb, hab, hzr', hyr']
        · rcases eq_or_ne b y with rfl | hby
          · simp [ha, hb, hab, hyz, hbr]
          · rcases eq_or_ne b z with rfl | hbz
            · simp [ha, hb, hab, hyz.symm, hbr]
            · simp [ha, hb, hab, hbr, hby, hbz]
      · have hab : a ≠ b := fun h => ha (h.symm ▸ hb)
        rcases eq_or_ne a r with rfl | har
        · simp [ha, hb, hab, hzr', hyr']
        · rcases eq_or_ne a y with rfl | hay
          · simp [ha, hb, hab, hyz, har]
          · rcases eq_or_ne a z with rfl | haz
            · simp [ha, hb, hab, hyz.symm, har]
            · simp [ha, hb, hab, har, hay, haz]
      · simp [ha, hb]

/-- Every K_{2,2}-code C on Fin n for n ≥ 4 satisfies (n - 2) * Set.ncard C ≤ 2 ^ (n.choose 2). -/
theorem k22_code_card_le (n : ℕ) (hn : 4 ≤ n)
    (C : Set (SimpleGraph (Fin n))) (hC : is_kst_code 2 2 n C) :
    (n - 2) * Set.ncard C ≤ 2 ^ n.choose 2 := by
  let u : Fin n := ⟨0, by omega⟩
  let v : Fin n := ⟨1, by omega⟩
  let r : Fin n := ⟨2, by omega⟩
  let A : Finset (Fin n) := {u, v}
  let R : Finset (Fin n) := Finset.univ \ A
  have huv : u ≠ v := by intro h; have := Fin.mk.inj h; contradiction
  have hA : A.card = 2 := Finset.card_pair huv
  have hR : R.card = n - 2 := by
    have h := Finset.card_sdiff_of_subset (Finset.subset_univ A)
    rw [Finset.card_univ, Fintype.card_fin, hA] at h
    exact h
  let H : Fin n → SimpleGraph (Fin n) := fun y =>
    if y = r then ⊥ else SimpleGraph.between (A : Set (Fin n)) (↑({r, y} : Finset (Fin n))) ⊤
  let f : SimpleGraph (Fin n) × Fin n → SimpleGraph (Fin n) := fun p => symmDiff p.1 (H p.2)
  have hinj : Set.InjOn f (C ×ˢ (R : Set (Fin n))) := by
    intro p1 hp1 p2 hp2 hf
    rcases p1 with ⟨G1, y1⟩
    rcases p2 with ⟨G2, y2⟩
    simp only [Set.mem_prod, Finset.mem_coe] at hp1 hp2
    have hG1 : G1 ∈ C := hp1.1
    have hy1 : y1 ∈ R := hp1.2
    have hG2 : G2 ∈ C := hp2.1
    have hy2 : y2 ∈ R := hp2.2
    dsimp [f] at hf
    have H_eq : symmDiff G1 G2 = symmDiff (H y1) (H y2) := by
      have H_cancel (x y z : SimpleGraph (Fin n)) : symmDiff (symmDiff x y) (symmDiff y z) = symmDiff x z := by
        rw [symmDiff_assoc, ← symmDiff_assoc y, symmDiff_self, bot_symmDiff]
      have h1 : symmDiff (symmDiff G1 (H y1)) (symmDiff (H y1) G2) = symmDiff (symmDiff G2 (H y2)) (symmDiff (H y1) G2) := by rw [hf]
      rw [H_cancel G1 (H y1) G2] at h1
      rw [symmDiff_comm G2 (H y2), symmDiff_comm (H y1) G2, H_cancel (H y2) G2 (H y1), symmDiff_comm (H y2) (H y1)] at h1
      exact h1
    by_cases hy : y1 = y2
    · subst hy
      rw [symmDiff_self, symmDiff_eq_bot] at H_eq
      ext <;> simp [H_eq]
    · exfalso
      have H_H := k22_code_card_le_H_symmDiff hn hy1 hy2 hy
      have hB : ({y1, y2} : Finset (Fin n)).card = 2 := Finset.card_pair hy
      have hy1A : y1 ∉ A := (Finset.mem_sdiff.mp hy1).2
      have hy2A : y2 ∉ A := (Finset.mem_sdiff.mp hy2).2
      have hdisj : Disjoint A {y1, y2} := by
        rw [Finset.disjoint_left]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (rfl | rfl)
        · exact hy1A hx
        · exact hy2A hx
      have hdiff : symmDiff G1 G2 = SimpleGraph.between (A : Set (Fin n)) (↑({y1, y2} : Finset (Fin n))) ⊤ :=
        H_eq.trans H_H
      have hG12 : G1 ≠ G2 := by
        intro heq
        subst heq
        rw [symmDiff_self] at hdiff
        have h_adj : (SimpleGraph.between (A : Set (Fin n)) (↑({y1, y2} : Finset (Fin n))) ⊤).Adj u y1 := by
          rw [SimpleGraph.between_adj, SimpleGraph.top_adj]
          refine ⟨fun h => hy1A (h ▸ Finset.mem_insert_self u {v}), Or.inl ⟨Finset.mem_insert_self u {v}, Finset.mem_insert_self y1 {y2}⟩⟩
        rw [← hdiff] at h_adj
        exact h_adj
      exact hC hG1 hG2 hG12 A {y1, y2} hdisj hA hB hdiff
  have h1 : Set.ncard (C ×ˢ (R : Set (Fin n))) ≤ Set.ncard (Set.univ : Set (SimpleGraph (Fin n))) := by
    have h_sub : f '' (C ×ˢ (R : Set (Fin n))) ⊆ Set.univ := Set.subset_univ _
    have h_le := Set.ncard_le_ncard h_sub
    rw [Set.InjOn.ncard_image hinj] at h_le
    exact h_le
  rw [Set.ncard_prod, Set.ncard_coe_finset, hR, mul_comm] at h1
  have h2 : Set.ncard (Set.univ : Set (SimpleGraph (Fin n))) = 2 ^ n.choose 2 := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, card_simpleGraph, Fintype.card_fin]
  omega
