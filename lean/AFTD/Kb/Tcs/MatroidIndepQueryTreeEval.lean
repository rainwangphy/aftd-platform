import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidIndepQueryTree

/-!
# MatroidIndepQueryTree.eval

Topic: algorithms   Node: 2e8c759a1130

Provenance: formalization of a published result. Source: arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier), Section 2 (the run of a deterministic independence-query algorithm)

The Boolean output of an independence-query decision tree T on a ground set α when the queries are answered by an oracle o : Finset α → Bool (o S = true meaning that S is independent). The arguments are the oracle o first, then the tree, and the value is a Boolean, defined by recursion on the tree: a leaf `leaf b` evaluates to b; a query node `query S no yes` evaluates to the value of the subtree `yes` (on the same oracle) if o S = true, and to the value of the subtree `no` otherwise.
-/

/-- The output of an independence-query tree when the oracle answers `o S` to the query `S`. -/
def MatroidIndepQueryTree.eval {α : Type*} (o : Finset α → Bool) : MatroidIndepQueryTree α → Bool
  | .leaf b => b
  | .query S no yes => if o S = true then yes.eval o else no.eval o
