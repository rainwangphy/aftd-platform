import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTreeBind
import AFTD.Kb.Tcs.ComparisonTreeDepth
import AFTD.Kb.Tcs.ComparisonTree

/-!
# comparison_tree_depth_bind_le

Topic: algorithms   Node: 9bc43aecbdf0

Provenance: helper lemma. step towards v_selection_16_8_upper_bound

If every continuation tree `f a` has depth at most `d`, then `comparison_tree_bind T f` has depth at most `comparison_tree_depth T + d`: comparison counts of staged algorithms add up.
-/

/-- Depth of a composed tree is at most the depth of the first stage plus a uniform bound on the continuations. -/
theorem comparison_tree_depth_bind_le {n : ℕ} (T : ComparisonTree n) (f : Fin n → ComparisonTree n)
    (d : ℕ) (h : ∀ a, comparison_tree_depth (f a) ≤ d) :
    comparison_tree_depth (comparison_tree_bind T f) ≤ comparison_tree_depth T + d := by
  induction T with
  | leaf a =>
    rw [comparison_tree_bind.eq_1, comparison_tree_depth.eq_1]
    simpa using h a
  | branch i j l r ih_l ih_r =>
    rw [comparison_tree_bind.eq_2, comparison_tree_depth.eq_2, comparison_tree_depth.eq_2]
    omega
