import AFTD.Prelude

/-!
# cyclic_cubic_synd_sets

Topic: quantum   Node: 2e79291045c7

Provenance: helper lemma. step towards cyclic_cubic_family_is_parity_repr

The set of Nat-level triples on which the cyclic cubic syndrome is 1: the triples {j,j+1,j+2} for j <= n-3, together with the two wraparound triples {n-2,n-1,0} and {n-1,0,1}.
-/

/-- The cyclic triples on n points, as a computable Finset of Finsets of naturals. -/
def cyclic_cubic_synd_sets (n : ℕ) : Finset (Finset ℕ) := ((Finset.range (n - 2)).image fun j => ({j, j + 1, j + 2} : Finset ℕ)) ∪ ({{n - 2, n - 1, 0}, {n - 1, 0, 1}} : Finset (Finset ℕ))
