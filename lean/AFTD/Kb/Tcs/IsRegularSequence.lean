import AFTD.Prelude

/-!
# IsRegularSequence

Topic: combinatorics   Node: c2da1d911f77

Provenance: formalization of a published result. Source: scout/2610-13103-additive-bases-and-the-zero-sum-invariant-mathsf-n-g-for-gr.md:93

A sequence S over an additive commutative group G is regular if for every proper additive subgroup H < G, the number of terms of S belonging to H is at most Nat.card H - 1.
-/

/-- A sequence S over G is regular if for every proper subgroup H < ⊤, |S ∩ H| ≤ |H| - 1. -/
def IsRegularSequence {G : Type*} [AddCommGroup G] (S : Multiset G) : Prop := open scoped Classical in
  ∀ H : AddSubgroup G, H < ⊤ → (S.filter (· ∈ H)).card ≤ Nat.card H - 1
