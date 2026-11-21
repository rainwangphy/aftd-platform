import AFTD.Prelude

/-!
# are_perm_isomorphic_families

Topic: combinatorics   Node: e134bb91a2f3

Provenance: formalization of a published result. Source: arXiv:2611.25346 Sec. 3

Two families of subsets of [n] are isomorphic if there is a permutation of [n] mapping one to the other.
-/

/-- Two set families on Fin n are isomorphic up to permutations of the ground set. -/
def are_perm_isomorphic_families (n : ℕ) (ℱ₁ ℱ₂ : Finset (Finset (Fin n))) : Prop := ∃ e : Equiv.Perm (Fin n), ℱ₂ = ℱ₁.image (fun A => A.image e)
