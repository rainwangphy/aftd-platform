import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8Adj

/-!
# poc8_cutb

Topic: fair_division   Node: adec0f9dce11

Boolean cut test: R is nonempty, R ⊆ S, S ⊄ R, and no edge leads from R to a vertex of S outside R.
-/

/-- Boolean test that `R` is a proper nonempty part of `S` closed under edges inside `S`. -/
def poc8_cutb (S R : Fin 8 → Bool) : Bool :=
  (List.finRange 8).any (fun v => R v) && (List.finRange 8).all (fun v => !R v || S v) &&
    (List.finRange 8).any (fun v => S v && !R v) &&
    (List.finRange 8).all (fun v => (List.finRange 8).all fun w => !S v || !R w || !poc8_adj w v || R v)
