import AFTD.Prelude

/-!
# MatroidIndepQueryTree

Topic: algorithms   Node: c2ff22702c3d

Provenance: formalization of a published result. Source: arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier), Section 2 (a deterministic algorithm using independence queries as a rooted binary decision tree)

A deterministic independence-query algorithm on a ground set α, as a rooted binary decision tree: a leaf `leaf b` outputs the Boolean b; an internal node `query S no yes` asks whether the finite set S ⊆ α is independent and continues with the subtree `no` if the answer is no and with the subtree `yes` if the answer is yes.
-/

/-- A deterministic independence-query algorithm as a binary decision tree: `leaf b` outputs `b`; `query S no yes` asks whether `S` is independent and continues with `no` or `yes`. -/
inductive MatroidIndepQueryTree (α : Type*) where | leaf (b : Bool) : MatroidIndepQueryTree α
  | query (S : Finset α) (no yes : MatroidIndepQueryTree α) : MatroidIndepQueryTree α
