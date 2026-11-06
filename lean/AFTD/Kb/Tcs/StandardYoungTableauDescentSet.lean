import AFTD.Prelude
import AFTD.Kb.Tcs.StandardYoungTableau
import AFTD.Kb.Tcs.StandardYoungTableauBox

/-!
# standard_young_tableau_descent_set

Topic: combinatorics   Node: 9b61e19b1b64

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 4.1

For a standard Young tableau T on D : Finset (ℕ × ℕ), the descent set standard_young_tableau_descent_set T is the subset of k ∈ Finset.Ico 1 D.card such that the cell T.box k has strictly smaller row index than the cell T.box (k+1).
-/

/-- The descent set of a standard Young tableau T: indices k such that the box for k+1 lies in a strictly lower row than the box for k. -/
def standard_young_tableau_descent_set {D : Finset (ℕ × ℕ)} (T : StandardYoungTableau D) : Finset ℕ := (Finset.Ico 1 D.card).filter fun k =>
  if hk : 1 ≤ k ∧ k < D.card then
    have h1 : k ∈ Finset.Icc 1 D.card := Finset.mem_Icc.mpr ⟨hk.1, le_of_lt hk.2⟩
    have h2 : k + 1 ∈ Finset.Icc 1 D.card := Finset.mem_Icc.mpr ⟨by omega, hk.2⟩
    (standard_young_tableau_box T k h1).1.1 < (standard_young_tableau_box T (k + 1) h2).1.1
  else false
