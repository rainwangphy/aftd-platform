import AFTD.Prelude
import AFTD.Kb.Tcs.Op861UnbalancedSelectorsImplyHypergraphCover
import AFTD.Kb.Tcs.Op861HypergraphCoverImpliesUnbalancedSelectors

/-!
# op861_unbalanced_selectors_hypergraph_iff

Topic: graphs   Node: eca8ad7f1f63

Provenance: helper lemma. Palette-surplus hypergraph reduction for OP-861; finite examples in experiment 30660.

For a palette of size k+r+s, proper selectors for (r+s+1)-sets and k-sets are equivalent to the stated uniform hypergraph coverage and avoidance system.
-/

theorem op861_unbalanced_selectors_hypergraph_iff
    (α : Type) [Fintype α] [DecidableEq α] (k r s : ℕ)
    (hn : Fintype.card α = k + r + s) :
    (∃ (f : {X : Finset α // X.card = r + s + 1} → α)
       (g : {T : Finset α // T.card = k} → α),
      (∀ X, f X ∈ X.1) ∧ (∀ T, g T ∈ T.1) ∧
      ∀ X T, (X.1 ∩ T.1).card ≤ r → f X ≠ g T) ↔
    ∃ H : α → Finset α → Prop,
      (∀ v Y, H v Y → Y.card = s + 1 ∧ v ∉ Y) ∧
      (∀ X : Finset α, X.card = r + s + 1 →
        ∃ v ∈ X, ∀ Y : Finset α, Y ⊆ X.erase v → Y.card = s + 1 → H v Y) ∧
      (∀ R : Finset α, R.card = r + s →
        ∃ v, v ∉ R ∧ ∀ Y : Finset α, H v Y → ¬ Y ⊆ R) := by
  constructor
  · rintro ⟨f, g, hf, hg, hproper⟩
    exact op861_unbalanced_selectors_imply_hypergraph_cover α k r s hn f g hf hg hproper
  · rintro ⟨H, _, hcover, havoid⟩
    exact op861_hypergraph_cover_implies_unbalanced_selectors α k r s hn H hcover havoid
