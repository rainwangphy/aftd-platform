import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutPinnedTwinsGraph

/-!
# maxcut_pinned_twins_not_colorable_three

Topic: equilibria   Node: d6595c6e0352

Provenance: helper lemma. Hypothesis check for the refutation of maxcut_op89_residual_exists (OP-89, arXiv:2610.04948).

The 182-vertex pinned twins graph maxcut_pinned_twins_graph is not 3-colorable.
-/

private instance maxcut_pinned_twins_not_colorable_three_dec :
    DecidableRel maxcut_pinned_twins_graph.Adj := by
  unfold maxcut_pinned_twins_graph
  infer_instance

theorem maxcut_pinned_twins_not_colorable_three : ¬ maxcut_pinned_twins_graph.Colorable 3 := by
  rintro ⟨C⟩
  have hfin : ∀ a b y z : Fin 3, y ≠ z → a ≠ y → a ≠ z → b ≠ y → b ≠ z → a = b := by decide
  have h1 : maxcut_pinned_twins_graph.Adj (.inr (1, 0), 0) (.inr (2, 0), 0) := by decide
  have h2 : maxcut_pinned_twins_graph.Adj (.inl 0, 0) (.inr (1, 0), 0) := by decide
  have h3 : maxcut_pinned_twins_graph.Adj (.inl 0, 0) (.inr (2, 0), 0) := by decide
  have h4 : maxcut_pinned_twins_graph.Adj (.inl 5, 0) (.inr (1, 0), 0) := by decide
  have h5 : maxcut_pinned_twins_graph.Adj (.inl 5, 0) (.inr (2, 0), 0) := by decide
  have h6 : maxcut_pinned_twins_graph.Adj (.inl 0, 0) (.inl 5, 0) := by decide
  exact C.valid h6 (hfin _ _ _ _ (C.valid h1) (C.valid h2) (C.valid h3) (C.valid h4) (C.valid h5))
