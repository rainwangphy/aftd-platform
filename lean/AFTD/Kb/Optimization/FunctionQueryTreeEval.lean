import AFTD.Prelude
import AFTD.Kb.Optimization.FunctionQueryTree

/-!
# function_query_tree_eval

Topic: submodular   Node: 818eb43c0b3d

Provenance: formalization of a published result. Source: arXiv:2611.02374 Sec. 2

Evaluates a function query tree on an input function f.
-/

/-- Evaluates a query tree on an input function f. -/
def function_query_tree_eval {α β : Type*} (t : FunctionQueryTree α β) (f : α → β) : Bool :=
  match t with
  | .leaf b => b
  | .query x next => function_query_tree_eval (next (f x)) f
