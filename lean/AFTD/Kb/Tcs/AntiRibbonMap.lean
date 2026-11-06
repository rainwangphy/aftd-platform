import AFTD.Prelude
import AFTD.Kb.Tcs.StandardYoungTableau
import AFTD.Kb.Tcs.StandardYoungTableauBox
import AFTD.Kb.Tcs.StandardYoungTableauDescentSet
import AFTD.Kb.Tcs.AntiRibbonDiagram

/-!
# anti_ribbon_map

Topic: combinatorics   Node: 44c2b18782d6

Provenance: formalization of a published result. Source: arXiv:2611.07715, Section 4

For a standard Young tableau T on D : Finset (ℕ × ℕ) and a filling M : D → ℕ, anti_ribbon_map T M is the filling of anti_ribbon_diagram D.card (standard_young_tableau_descent_set T) assigning to each cell p the value M(T.box k) where k = p.1.1 + p.1.2 - 1 if k ∈ Finset.Icc 1 D.card, and 0 otherwise.
-/

/-- The anti-ribbon filling R_T(M) assigning the entry of M at box T⁻¹(k) to the k-th box of the anti-ribbon shape. -/
def anti_ribbon_map {D : Finset (ℕ × ℕ)} (T : StandardYoungTableau D)
    (M : D → ℕ) : (anti_ribbon_diagram D.card (standard_young_tableau_descent_set T)) → ℕ := fun p =>
  let k := p.1.1 + p.1.2 - 1
  if hk : k ∈ Finset.Icc 1 D.card then
    M (standard_young_tableau_box T k hk)
  else 0
