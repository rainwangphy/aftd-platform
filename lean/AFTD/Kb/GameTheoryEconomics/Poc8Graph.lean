import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8Adj

/-!
# poc8_graph

Topic: fair_division   Node: 0479b214f61a

The 8-vertex graph G with edges 04, 05, 06, 07, 13, 15, 16, 17, 23, 24, 26, 27, 36, 37, 45, 47, 57, 67.
-/

/-- The 8-vertex counterexample graph. -/
def poc8_graph : SimpleGraph (Fin 8) :=
  { Adj := fun a b => poc8_adj a b = true
    symm := ⟨by decide⟩
    loopless := ⟨by decide⟩ }
