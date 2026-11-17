import AFTD.Prelude

/-!
# bipartite_matchings

Topic: graphs   Node: 7922798977b6

Provenance: helper lemma. Defined for OP-1789 (size-priority matching noise phase transition), building on arXiv:2601.20502 (Optimal matching under size priority), Section 1.

For a bipartite graph with left vertices Fin n and right vertices Fin n whose edge set is E (a finite set of pairs (left, right)), the finite set of its matchings: the subsets M of E in which any two edges sharing a left endpoint or sharing a right endpoint are equal.
-/

def bipartite_matchings (n : ℕ) (E : Finset (Fin n × Fin n)) : Finset (Finset (Fin n × Fin n)) :=
  E.powerset.filter (fun M => ∀ e ∈ M, ∀ f ∈ M, (e.1 = f.1 ∨ e.2 = f.2) → e = f)
