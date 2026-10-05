import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8Close

/-!
# poc8_connb

Topic: fair_division   Node: f4e8bd19368f

Boolean connectivity test: some vertex r of S reaches every vertex of S within 7 BFS steps inside S.
-/

/-- Boolean test: some `r ∈ S` reaches all of `S` in 7 BFS steps inside `S`. -/
def poc8_connb (S : Fin 8 → Bool) : Bool :=
  (List.finRange 8).any fun r =>
    S r && (List.finRange 8).all fun v => !S v || poc8_close S (fun w => w == r) 7 v
