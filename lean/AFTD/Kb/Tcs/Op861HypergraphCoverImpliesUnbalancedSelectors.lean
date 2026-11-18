import AFTD.Prelude

/-!
# op861_hypergraph_cover_implies_unbalanced_selectors

Topic: graphs   Node: 3e62748ac3a5

Provenance: helper lemma. Palette-surplus hypergraph reduction for OP-861; finite examples in experiment 30660.

Uniform hypergraph coverage and avoidance conditions give proper selectors for (r+s+1)-sets and k-sets.
-/

theorem op861_hypergraph_cover_implies_unbalanced_selectors
    (α : Type) [Fintype α] [DecidableEq α] (k r s : ℕ)
    (hn : Fintype.card α = k + r + s)
    (H : α → Finset α → Prop)
    (hcover : ∀ X : Finset α, X.card = r + s + 1 →
      ∃ v ∈ X, ∀ Y : Finset α, Y ⊆ X.erase v → Y.card = s + 1 → H v Y)
    (havoid : ∀ R : Finset α, R.card = r + s →
      ∃ v, v ∉ R ∧ ∀ Y : Finset α, H v Y → ¬ Y ⊆ R) :
    ∃ (f : {X : Finset α // X.card = r + s + 1} → α)
      (g : {T : Finset α // T.card = k} → α),
      (∀ X, f X ∈ X.1) ∧ (∀ T, g T ∈ T.1) ∧
      ∀ X T, (X.1 ∩ T.1).card ≤ r → f X ≠ g T := by
  classical
  let R (T : {T : Finset α // T.card = k}) : Finset α := Finset.univ \ T.1
  have hR (T : {T : Finset α // T.card = k}) : (R T).card = r + s := by
    have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T.1)
    simp only [Finset.card_univ, T.2, hn] at hh
    dsimp [R]
    omega
  let f : {X : Finset α // X.card = r + s + 1} → α :=
    fun X => Classical.choose (hcover X.1 X.2)
  let g : {T : Finset α // T.card = k} → α :=
    fun T => Classical.choose (havoid (R T) (hR T))
  have hf (X : {X : Finset α // X.card = r + s + 1}) : f X ∈ X.1 :=
    (Classical.choose_spec (hcover X.1 X.2)).1
  have hg (T : {T : Finset α // T.card = k}) : g T ∈ T.1 := by
    have h := (Classical.choose_spec (havoid (R T) (hR T))).1
    simpa [R, g] using h
  refine ⟨f, g, hf, hg, ?_⟩
  intro X T hint heq
  let W : Finset α := X.1 \ T.1
  have hW : s + 1 ≤ W.card := by
    have hcard := Finset.card_sdiff_add_card_inter X.1 T.1
    dsimp [W]
    omega
  obtain ⟨Y, hYW, hYcard⟩ := Finset.exists_subset_card_eq hW
  have hYXR : Y ⊆ X.1.erase (f X) := by
    intro y hy
    have hyW := Finset.mem_sdiff.mp (hYW hy)
    apply Finset.mem_erase.mpr
    refine ⟨?_, hyW.1⟩
    intro hey
    apply hyW.2
    rw [hey, heq]
    exact hg T
  have hYR : Y ⊆ R T := by
    intro y hy
    have hyW := Finset.mem_sdiff.mp (hYW hy)
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyW.2⟩
  have hHY : H (f X) Y := (Classical.choose_spec (hcover X.1 X.2)).2 Y hYXR hYcard
  have hbad : H (g T) Y → ¬ Y ⊆ R T :=
    (Classical.choose_spec (havoid (R T) (hR T))).2 Y
  rw [← heq] at hbad
  exact hbad hHY hYR
