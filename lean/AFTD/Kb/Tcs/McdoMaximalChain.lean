import AFTD.Prelude

/-!
# mcdo_maximal_chain

Topic: combinatorics   Node: dfc58ba376ce

Provenance: formalization of a published result. Source: arXiv:2611.26888 (structure of linear extensions of posets and lexicographic shellings), Section 2.2 (maximal chains of J(P)); the encoding by addition orders is standard.

For a finite poset P with n = |P| elements, the type of maximal chains of the lattice J(P) of order ideals, encoded as the subtype of functions e : Fin n → P such that e is bijective and e i < e j implies i < j. Such an e lists the elements of P in the order they are added along the chain ∅ = I_0 ⋖ I_1 ⋖ ... ⋖ I_n = P, with I_i = {e 0, ..., e (i-1)}; maximal chains of J(P) correspond bijectively to these orderings.
-/

def mcdo_maximal_chain (P : Type*) [PartialOrder P] [Fintype P] : Type _ :=
  {e : Fin (Fintype.card P) → P // Function.Bijective e ∧ ∀ i j, e i < e j → i < j}
