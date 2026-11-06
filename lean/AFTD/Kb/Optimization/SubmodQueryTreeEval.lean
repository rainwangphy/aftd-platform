import AFTD.Prelude
import AFTD.Kb.Optimization.CubeFunc
import AFTD.Kb.Optimization.SubmodQueryTree

/-!
# submod_query_tree_eval

Topic: submodular   Node: adec4e90bf51

Provenance: formalization of a published result. Source: arXiv:2611.02374, Def. 2.5

Evaluates a query decision tree on a function f by querying coordinates along the tree path until reaching a leaf.
-/

/-- Evaluate a query decision tree on a function from the hypercube. -/
def submod_query_tree_eval {n k d : ℕ} (T : SubmodQueryTree n k d) (f : CubeFunc n k) : Bool := match T with
  | .leaf b => b
  | .query x next => submod_query_tree_eval (next (f x)) f
