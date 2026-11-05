import AFTD.Prelude

/-!
# booleanTopForm

Topic: combinatorics   Node: e26fa7ff5880

Provenance: formalization of a published result. Source: arXiv:2611.03452, Lemma 2.7

Given a type V with an additive commutative group structure [AddCommGroup V], a natural number d, a function p : V → ZMod 2, and a tuple h : Fin d → V, booleanTopForm d p h is defined as the sum in ZMod 2 over all subsets S : Finset (Fin d) of p (∑ i ∈ S, h i).
-/

open scoped BigOperators in
/-- The top form Delta^d p of p : V -> ZMod 2 evaluated at directions h_0, ..., h_{d-1}. -/
def booleanTopForm {V : Type*} [AddCommGroup V] (d : ℕ)
    (p : V → ZMod 2) (h : Fin d → V) : ZMod 2 := ∑ S : Finset (Fin d), p (∑ i ∈ S, h i)
