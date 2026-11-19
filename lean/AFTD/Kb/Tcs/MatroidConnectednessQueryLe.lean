import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidIndepQueryTree
import AFTD.Kb.Tcs.MatroidIndepQueryTreeDepth
import AFTD.Kb.Tcs.MatroidIndepQueryTreeEval
import AFTD.Kb.Tcs.MatroidConnected

/-!
# matroid_connectedness_query_le

Topic: algorithms   Node: 4c9f1463ba98

Provenance: formalization of a published result. Source: arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier), Section 2 and Problem (A) (query complexity of deciding matroid connectedness in the independence oracle model; the ground set is Fin n)

For natural numbers n and q, matroid_connectedness_query_le n q is the statement that the deterministic independence-query complexity of deciding matroid connectedness on n elements is at most q: there is an independence-query decision tree T on the ground set Fin n (a MatroidIndepQueryTree (Fin n)) of depth (MatroidIndepQueryTree.depth) at most q such that for every matroid M on the type Fin n whose ground set M.E is all of Fin n, and every oracle o : Finset (Fin n) → Bool that is the independence oracle of M (for every finite set S, o S = true if and only if S is independent in M), the output of T on o (MatroidIndepQueryTree.eval o T) is true if and only if M is connected (matroid_connected M: any two distinct elements lie in a common circuit).
-/

/-- `D(n) ≤ q`: some deterministic independence-query algorithm of depth at most `q` decides connectedness of every matroid with ground set `Fin n`. -/
def matroid_connectedness_query_le (n q : ℕ) : Prop :=
  ∃ T : MatroidIndepQueryTree (Fin n), T.depth ≤ q ∧
    ∀ M : Matroid (Fin n), M.E = Set.univ → ∀ o : Finset (Fin n) → Bool,
      (∀ S : Finset (Fin n), o S = true ↔ M.Indep (S : Set (Fin n))) →
      (T.eval o = true ↔ matroid_connected M)
