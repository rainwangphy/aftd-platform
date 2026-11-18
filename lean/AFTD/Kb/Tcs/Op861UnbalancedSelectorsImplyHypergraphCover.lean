import AFTD.Prelude

/-!
# op861_unbalanced_selectors_imply_hypergraph_cover

Topic: graphs   Node: 93f92e4b7c15

Provenance: helper lemma. Palette-surplus hypergraph reduction for OP-861; finite examples in experiment 30660.

A proper pair of selectors for (r+s+1)-sets and k-sets produces uniform hypergraph families satisfying the coverage and avoidance conditions.
-/

theorem op861_unbalanced_selectors_imply_hypergraph_cover
    (α : Type) [Fintype α] [DecidableEq α] (k r s : ℕ)
    (hn : Fintype.card α = k + r + s)
    (f : {X : Finset α // X.card = r + s + 1} → α)
    (g : {T : Finset α // T.card = k} → α)
    (hf : ∀ X, f X ∈ X.1) (hg : ∀ T, g T ∈ T.1)
    (hproper : ∀ X T, (X.1 ∩ T.1).card ≤ r → f X ≠ g T) :
    ∃ H : α → Finset α → Prop,
      (∀ v Y, H v Y → Y.card = s + 1 ∧ v ∉ Y) ∧
      (∀ X : Finset α, X.card = r + s + 1 →
        ∃ v ∈ X, ∀ Y : Finset α, Y ⊆ X.erase v → Y.card = s + 1 → H v Y) ∧
      (∀ R : Finset α, R.card = r + s →
        ∃ v, v ∉ R ∧ ∀ Y : Finset α, H v Y → ¬ Y ⊆ R) := by
  classical
  let H : α → Finset α → Prop := fun v Y =>
    Y.card = s + 1 ∧ v ∉ Y ∧
      ∃ (X : Finset α) (hX : X.card = r + s + 1),
        f ⟨X, hX⟩ = v ∧ Y ⊆ X.erase v
  refine ⟨H, ?_, ?_, ?_⟩
  · intro v Y h
    exact ⟨h.1, h.2.1⟩
  · intro X hX
    let v := f ⟨X, hX⟩
    refine ⟨v, hf ⟨X, hX⟩, ?_⟩
    intro Y hYX hY
    refine ⟨hY, ?_, X, hX, rfl, hYX⟩
    intro hv
    exact (Finset.mem_erase.mp (hYX hv)).1 rfl
  · intro R hR
    let T : Finset α := Finset.univ \ R
    have hTk : T.card = k := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ R)
      simp only [Finset.card_univ, hR, hn] at hh
      dsimp [T]
      omega
    let t : {T : Finset α // T.card = k} := ⟨T, hTk⟩
    let v := g t
    have hvT : v ∈ T := hg t
    have hvR : v ∉ R := (Finset.mem_sdiff.mp hvT).2
    refine ⟨v, hvR, ?_⟩
    intro Y hY hYR
    obtain ⟨hYcard, _, X, hX, hfX, hYX⟩ := hY
    have hYX' : Y ⊆ X := hYX.trans (Finset.erase_subset _ _)
    have hd : Disjoint Y (X ∩ T) := by
      apply Finset.disjoint_left.mpr
      intro w hwY hwXT
      have hwT := (Finset.mem_inter.mp hwXT).2
      exact (Finset.mem_sdiff.mp hwT).2 (hYR hwY)
    have hc : (Y ∪ (X ∩ T)).card ≤ X.card :=
      Finset.card_le_card (Finset.union_subset hYX' Finset.inter_subset_left)
    rw [Finset.card_union_of_disjoint hd, hYcard, hX] at hc
    have hint : (X ∩ T).card ≤ r := by omega
    exact (hproper ⟨X, hX⟩ t hint) hfX
