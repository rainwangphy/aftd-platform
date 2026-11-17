import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.TreeGameEdge

/-!
# enc1385BlockMoves

Topic: automata   Node: 5d7c59cb9ee3

Provenance: helper lemma. Block replay for arXiv:2611.10136, Conjecture 19.

The phase-game actions for one original edge, with the original priority on the final bit and priority zero on preceding bits.
-/

noncomputable def enc1385BlockMoves {Q : Type} [Fintype Q] (e : TreeGameEdge Q 3) :
    List (Bool × Fin 3) :=
  (List.range (Fintype.card Q + 1)).map fun i =>
    ((enc1385Block e).getD i false, if i = Fintype.card Q then e.prio else 0)
