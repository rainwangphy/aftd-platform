import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseIsScaling
import AFTD.Kb.GameTheoryEconomics.FseMapsToDomain
import AFTD.Kb.GameTheoryEconomics.FseSP
import AFTD.Kb.GameTheoryEconomics.FseSurjective
import AFTD.Kb.GameTheoryEconomics.FseAnonymous
import AFTD.Kb.GameTheoryEconomics.FseDictatorship
import AFTD.Kb.GameTheoryEconomics.FseSinglePeaked
import AFTD.Kb.GameTheoryEconomics.FseLeftmost
import AFTD.Kb.GameTheoryEconomics.FseQ0
import AFTD.Kb.GameTheoryEconomics.FseLeftmostMapsTo
import AFTD.Kb.GameTheoryEconomics.FseLeftmostSPOfAntitone
import AFTD.Kb.GameTheoryEconomics.FseQ0IsScaling
import AFTD.Kb.GameTheoryEconomics.FseQ0Antitone
import AFTD.Kb.GameTheoryEconomics.FseQ0NotSinglePeaked
import AFTD.Kb.GameTheoryEconomics.FseLeftmostSurjective
import AFTD.Kb.GameTheoryEconomics.FseLeftmostAnonymous
import AFTD.Kb.GameTheoryEconomics.FseLeftmostNotDictatorship

/-!
# fse_dictatorship_conjecture_false

Topic: mechanism_design   Node: 9c81989eac60

Refutation of the dictatorship conjecture of arXiv 2402.18908 (Section 8). For every number n ≥ 2 of agents there is a scaling function (namely q(y) = 1 - 9y/10) under which some agent's preference is not single-peaked, and yet there is a deterministic mechanism into [0,1] that is strategyproof, surjective and anonymous but is not a dictatorship (the leftmost mechanism).
-/

/-- **Refutation of the dictatorship conjecture of arXiv 2402.18908 (Section 8).** For every number `n ≥ 2` of agents there is a scaling function (namely `q(y) = 1 - 9y/10`) under which some agent's preference is not single-peaked, and yet there is a deterministic mechanism into `[0,1]` that is strategyproof, surjective and anonymous but is not a dictatorship (the leftmost mechanism). -/
theorem fse_dictatorship_conjecture_false (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    ∃ q : ℝ → ℝ, fse_IsScaling q ∧ (∃ x ∈ Set.Icc (0 : ℝ) 1, ¬ fse_SinglePeaked q x) ∧
      ∃ f : (Fin n → ℝ) → ℝ, fse_MapsToDomain f ∧ fse_SP q f ∧ fse_Surjective f ∧
        fse_Anonymous f ∧ ¬ fse_Dictatorship f :=
  ⟨fse_q0, fse_q0_isScaling, ⟨0, by norm_num, fse_q0_not_singlePeaked⟩,
    fse_leftmost, fse_leftmost_mapsTo,
    fse_leftmost_SP_of_antitone fse_q0 fse_q0_antitone
      (fun y hy => le_of_lt (fse_q0_isScaling.2 y hy)),
    fse_leftmost_surjective, fse_leftmost_anonymous, fse_leftmost_not_dictatorship hn⟩
