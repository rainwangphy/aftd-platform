import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseIsScaling
import AFTD.Kb.GameTheoryEconomics.FseQ0

/-!
# fse_q0_isScaling

Topic: mechanism_design   Node: 8eb92af50ca0

q0(y) = 1 - 9y/10 is a scaling function (continuous and positive on [0,1]).
-/

/-- `q0(y) = 1 - 9y/10` is a scaling function (continuous and positive on `[0,1]`). -/
lemma fse_q0_isScaling : fse_IsScaling fse_q0 := by
  refine ⟨?_, ?_⟩
  · unfold fse_q0; fun_prop
  · intro y hy; unfold fse_q0; nlinarith [hy.1, hy.2]
