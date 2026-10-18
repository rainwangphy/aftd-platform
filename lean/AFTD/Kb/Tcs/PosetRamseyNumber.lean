import AFTD.Prelude
import AFTD.Kb.Tcs.PosetRamseyProperty

/-!
# poset_ramsey_number

Topic: combinatorics   Node: 5803f1115a4f

Provenance: formalization of a published result. Source: arXiv:2610.20545, The k-color poset Ramsey number of the diamond is 2k

The k-color poset Ramsey number of a preordered type P is the infimum of the set of natural numbers d such that every k-coloring of the Boolean lattice Finset (Fin d) contains a monochromatic induced copy of P.
-/

/-- The poset Ramsey number R_k(P): the minimum dimension d such that the Boolean lattice on Fin d has the k-color Ramsey property for P. -/
noncomputable def poset_ramsey_number (P : Type*) [Preorder P] (k : ℕ) : ℕ :=
  sInf {d : ℕ | poset_ramsey_property P k d}
