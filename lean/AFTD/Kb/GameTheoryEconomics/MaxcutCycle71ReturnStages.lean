import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71ReturnRank
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71Coloring

/-!
# maxcut_cycle71_return_stages

Topic: equilibria   Node: 64d2293302aa

Provenance: helper lemma. The explicit 71-vertex unweighted minimal-deviation cycle for the potential-function question in arXiv:1810.09278, Section 7; experiments 12443, 12444, 12450 and 12452.

The 33 profiles of the displayed 71-vertex cycle: the initial profile, the joint deviation, and the partial singleton restorations.
-/

def maxcut_cycle71_return_stages (i : Fin 33) (v : Fin 71) : Fin 3 :=
  if i.val = 0 ∨ (v.val < 32 ∧ maxcut_cycle71_return_rank v < i.val - 1) then
    maxcut_cycle71_coloring 0 v
  else maxcut_cycle71_coloring 1 v
