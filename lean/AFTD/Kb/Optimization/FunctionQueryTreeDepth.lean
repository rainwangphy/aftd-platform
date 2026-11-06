import AFTD.Prelude
import AFTD.Kb.Optimization.FunctionQueryTree

/-!
# function_query_tree_depth

Topic: submodular   Node: 67999e4b93aa

Provenance: formalization of a published result. Source: arXiv:2611.02374 Sec. 2

The maximum number of queries made by a query tree over all possible oracle responses.
-/

/-- Worst-case query depth of a query tree. -/
def function_query_tree_depth {α β : Type*} [Fintype β] (t : FunctionQueryTree α β) : ℕ :=
  match t with
  | .leaf _ => 0
  | .query _ next => 1 + Finset.sup Finset.univ (fun y => function_query_tree_depth (next y))
