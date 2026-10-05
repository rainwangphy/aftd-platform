import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseQ0

/-!
# fse_q0_antitone

Topic: mechanism_design   Node: d1ec5dbe7b78

q0 is non-increasing on [0,1].
-/

/-- `q0` is non-increasing on `[0,1]`. -/
lemma fse_q0_antitone : AntitoneOn fse_q0 (Set.Icc 0 1) := by
  intro a _ b _ hab; unfold fse_q0; nlinarith
