import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPartialMajorityColoring

/-!
# MajorityGameAliceWinsFrom

Topic: combinatorial_games   Node: a737026de3ca

Provenance: formalization of a published result. Source: arXiv:2611.32746: The majority game chromatic number for dense random graphs

In the two-colour majority colouring game on a finite graph G, Alice can win from a partial colouring c if all vertices are coloured, or on Alice's turn (an even number of coloured vertices) there is an uncoloured vertex and colour yielding a valid majority colouring from which Alice can win, or on Bob's turn (an odd number of coloured vertices) Bob has a legal move and for every legal move of Bob, Alice can win.
-/

/-- Alice can win the two-colour majority game from a partial colouring c. -/
inductive MajorityGameAliceWinsFrom {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : (V → Option Bool) → Prop where
  | full (c : V → Option Bool) :
      (∀ v, (c v).isSome) →
      MajorityGameAliceWinsFrom G c
  | alice_turn (c : V → Option Bool) (v : V) (col : Bool)
      (heven : Even (Finset.filter (fun u => (c u).isSome) Finset.univ).card)
      (hnone : c v = none)
      (hlegal : is_partial_majority_coloring G (Function.update c v (some col)))
      (hwin : MajorityGameAliceWinsFrom G (Function.update c v (some col))) :
      MajorityGameAliceWinsFrom G c
  | bob_turn (c : V → Option Bool)
      (hodd : Odd (Finset.filter (fun u => (c u).isSome) Finset.univ).card)
      (hex : ∃ (v : V) (col : Bool), c v = none ∧ is_partial_majority_coloring G (Function.update c v (some col)))
      (hall : ∀ (v : V) (col : Bool), c v = none →
        is_partial_majority_coloring G (Function.update c v (some col)) →
        MajorityGameAliceWinsFrom G (Function.update c v (some col))) :
      MajorityGameAliceWinsFrom G c
