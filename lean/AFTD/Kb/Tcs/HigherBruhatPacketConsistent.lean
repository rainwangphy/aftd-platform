import AFTD.Prelude

/-!
# higher_bruhat_packet_consistent

Topic: combinatorics   Node: cd47f00e34d9

Provenance: formalization of a published result. Source: arXiv:2611.17465 Definition 1

A family X of subsets of {0, ..., n-1} is packet-consistent if for every subset M ⊆ {0, ..., n-1} of size k+2, the family X satisfies either that M \ {a} ∈ X implies M \ {b} ∈ X for all a < b in M, or that M \ {b} ∈ X implies M \ {a} ∈ X for all a < b in M.
-/

/-- A family X of (k+1)-subsets of Fin n is packet-consistent if its intersection with each packet forms an initial or final segment. -/
def higher_bruhat_packet_consistent (n k : ℕ) (X : Finset (Finset (Fin n))) : Prop :=
  ∀ M : Finset (Fin n), M.card = k + 2 →
    (∀ a ∈ M, ∀ b ∈ M, a < b → M.erase a ∈ X → M.erase b ∈ X) ∨
    (∀ a ∈ M, ∀ b ∈ M, a < b → M.erase b ∈ X → M.erase a ∈ X)
