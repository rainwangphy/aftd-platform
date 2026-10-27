import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.OrderedTriple
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# fin_triples

Topic: np_completeness   Node: db276d3b783b

Provenance: formalization of a published result. Source: arXiv:2610.03808 Sec. 2

The list of all ordered triples (a, b, c) of elements of Fin m satisfying a < b < c.
-/

/-- List of all ordered triples in Fin m in lexicographical order. -/
def fin_triples (m : ℕ) : List (OrderedTriple (Fin m)) :=
  (List.finRange m).flatMap fun a =>
    (List.finRange m).flatMap fun b =>
      (List.finRange m).filterMap fun c =>
        if hab : a < b then
          if hbc : b < c then
            some ⟨a, b, c, hab, hbc⟩
          else none
        else none
