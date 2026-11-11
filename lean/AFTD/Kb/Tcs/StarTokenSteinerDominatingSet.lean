import AFTD.Prelude

/-!
# star_token_steiner_dominating_set

Topic: graphs   Node: dd9405ef5fb7

Provenance: formalization of a published result. Source: arXiv:2611.11191, Theorem 6.2

For an implicit natural number k and a set S : Set (Finset (Fin (2 * k - 1))), star_token_steiner_dominating_set S is the set of elements v of the subtype { s : Finset (Option (Fin (2 * k - 1))) // s.card = k } such that there exists some X ∈ S with v.val = insert none (X.image some) or v.val = (Finset.univ \ X).image some.
-/

/-- Candidate perfect dominating set in F_k(S_{2k-1}) constructed from a set of blocks S. -/
def star_token_steiner_dominating_set {k : ℕ} (S : Set (Finset (Fin (2 * k - 1)))) :
    Set { s : Finset (Option (Fin (2 * k - 1))) // s.card = k } := { v | ∃ X ∈ S, v.val = insert none (X.image some) ∨ v.val = (Finset.univ \ X).image some }
