import AFTD.Prelude
import AFTD.Kb.Tcs.TgreedyRcOutput
import AFTD.Kb.Tcs.MgreedyRcStep
import AFTD.Kb.Tcs.StringOverlapLen
import AFTD.Kb.Tcs.GreedyRcStep
import AFTD.Kb.Tcs.RevComp
import AFTD.Kb.Tcs.StringOverlapMerge

/-!
# tgreedy_rc_output_sanity

Topic: approximation   Node: 234783e3869e

Provenance: helper lemma. Sanity check of tgreedy_rc_output (arXiv:2611.16573)

With cm = id, TGREEDY-RC on {12} can output 12.
-/

theorem tgreedy_rc_output_sanity : tgreedy_rc_output id ({[1, 2]} : Finset (List ℕ)) [1, 2] :=
  ⟨{[1, 2]}, Relation.ReflTransGen.single (by unfold mgreedy_rc_step; decide),
    Relation.ReflTransGen.refl⟩
