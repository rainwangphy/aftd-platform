import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidIndepQueryTree

/-!
# MatroidIndepQueryTree.depth

Topic: algorithms   Node: 7096e8d9070c

Provenance: formalization of a published result. Source: arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier), Section 2 (query complexity = maximum height of the decision tree)

The depth (height) of an independence-query decision tree on a ground set α, a natural number defined by recursion on the tree: a leaf `leaf b` has depth 0, and a query node `query S no yes` has depth 1 + max(depth of the subtree no, depth of the subtree yes). It is the largest number of queries on a root-to-leaf path.
-/

/-- The height of an independence-query tree: the largest number of queries on a root-to-leaf path. -/
def MatroidIndepQueryTree.depth {α : Type*} : MatroidIndepQueryTree α → ℕ
  | .leaf _ => 0
  | .query _ no yes => 1 + max no.depth yes.depth
