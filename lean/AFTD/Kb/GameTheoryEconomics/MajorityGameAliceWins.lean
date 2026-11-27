import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MajorityGameAliceWinsFrom

/-!
# majority_game_alice_wins

Topic: combinatorial_games   Node: 80774d55f988

Provenance: formalization of a published result. Source: arXiv:2611.32746: The majority game chromatic number for dense random graphs

Alice has a winning strategy in the two-colour majority colouring game on G if she can win starting from the completely uncoloured graph.
-/

/-- Alice has a winning strategy in the two-colour majority colouring game on G. -/
def majority_game_alice_wins {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop := MajorityGameAliceWinsFrom G (fun _ => none)
