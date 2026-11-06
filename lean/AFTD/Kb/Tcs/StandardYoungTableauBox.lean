import AFTD.Prelude
import AFTD.Kb.Tcs.StandardYoungTableau

/-!
# standard_young_tableau_box

Topic: combinatorics   Node: 1b0dee496967

Provenance: formalization of a published result. Source: arXiv:2611.07715, Section 4

For a standard Young tableau T on a finite diagram D : Finset (ℕ × ℕ) and an integer k with proof hk : k ∈ Finset.Icc 1 D.card, standard_young_tableau_box T k hk is the cell in D given by T.toEquiv.symm ⟨k, hk⟩.
-/

/-- The box of D assigned entry k by a standard Young tableau T. -/
def standard_young_tableau_box {D : Finset (ℕ × ℕ)} (T : StandardYoungTableau D) (k : ℕ) (hk : k ∈ Finset.Icc 1 D.card) : D := T.toEquiv.symm ⟨k, hk⟩
