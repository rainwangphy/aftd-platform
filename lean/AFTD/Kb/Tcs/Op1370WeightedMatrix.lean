import AFTD.Prelude

/-!
# op1370_weighted_matrix

Topic: combinatorics   Node: ccc345326f8c

Provenance: helper lemma.

The signed weighted-incidence matrix of a finite family, with a fixed additive matrix.
-/

open Finset Matrix Polynomial
open scoped BigOperators

noncomputable def op1370_weighted_matrix
    {α V K : Type*} [DecidableEq α] [Fintype α] [Field K]
    (A : V → Finset α) (J : Matrix V V K) (q : Finset α → K) : Matrix V V K :=
  fun a b => J a b + ∑ X : Finset α, q X *
    ((if A a ⊆ X then (-1 : K) ^ (X \ A a).card else 0) * (if X ⊆ A b then 1 else 0))
