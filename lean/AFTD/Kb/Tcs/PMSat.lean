import AFTD.Prelude
import AFTD.Kb.Tcs.PMAns
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PMPosetAns

/-!
# PMSat

Topic: algorithms   Node: 3b46a6d50957

A list of query/answer facts is satisfied by P.
-/

/-- A list of query/answer facts is satisfied by `P`. -/
def PMSat {n : ℕ} (P : PMPoset n) (F : List (Fin n × Fin n × PMAns)) : Prop :=
  ∀ f ∈ F, P.ans f.1 f.2.1 = f.2.2
