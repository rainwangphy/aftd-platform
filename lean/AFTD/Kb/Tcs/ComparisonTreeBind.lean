import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTree

/-!
# comparison_tree_bind

Topic: algorithms   Node: 37812dac1fb5

Provenance: helper lemma. step towards v_selection_16_8_upper_bound

Composition of comparison decision trees: run `T`, and at each leaf `a` continue with the tree `f a`. Recursion peels off the first stage and appends a continuation stage below each leaf.
-/

/-- Sequential composition of comparison trees: `comparison_tree_bind T f` runs the first stage `T` and then the continuation `f a` selected by the returned index. -/
def comparison_tree_bind {n : ℕ} : ComparisonTree n → (Fin n → ComparisonTree n) → ComparisonTree n := fun T f =>
  match T with
  | .leaf a => f a
  | .branch i j l r => .branch i j (comparison_tree_bind l f) (comparison_tree_bind r f)
