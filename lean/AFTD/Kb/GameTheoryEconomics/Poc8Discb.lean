import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8Close
import AFTD.Kb.GameTheoryEconomics.Poc8Cutb

/-!
# poc8_discb

Topic: fair_division   Node: ffb2de97a0a3

Boolean disconnectedness test: S is empty, or the BFS closure inside S of some vertex of S is a proper cut of S.
-/

/-- Boolean test: `S` is empty or the BFS closure of some vertex of `S` is a proper cut of `S`. -/
def poc8_discb (S : Fin 8 → Bool) : Bool :=
  (List.finRange 8).all (fun v => !S v) ||
    (List.finRange 8).any fun r => S r && poc8_cutb S (poc8_close S (fun w => w == r) 7)
