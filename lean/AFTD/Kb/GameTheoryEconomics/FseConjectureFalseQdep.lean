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
import AFTD.Kb.GameTheoryEconomics.FseQ0Antitone
import AFTD.Kb.GameTheoryEconomics.FseQ0NotSinglePeaked
import AFTD.Kb.GameTheoryEconomics.FseLeftmostSurjective
import AFTD.Kb.GameTheoryEconomics.FseLeftmostAnonymous
import AFTD.Kb.GameTheoryEconomics.FseLeftmostNotDictatorship
import AFTD.Kb.GameTheoryEconomics.FseF
import AFTD.Kb.GameTheoryEconomics.FseDictatorSP

/-!
# fse_conjecture_false_qdep

Topic: mechanism_design   Node: 22414be41637

Refutation in the model with the scaling function as input. The mechanism fse_F (which receives q) is strategyproof and surjective for every scaling function, yet it is not a dictatorship: for q(y) = 1 - 9y/10, under which some agent's preference is not single-peaked, it is the (anonymous) leftmost mechanism.
-/

/-- **Refutation in the model with the scaling function as input.** The mechanism `fse_F` (which receives `q`) is strategyproof and surjective for every scaling function, yet it is not a dictatorship: for `q(y) = 1 - 9y/10`, under which some agent's preference is not single-peaked, it is the (anonymous) leftmost mechanism. -/
theorem fse_conjecture_false_qdep (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (∀ q : ℝ → ℝ, fse_IsScaling q →
        fse_SP q (fse_F (n := n) q) ∧ fse_Surjective (fse_F (n := n) q) ∧
        fse_MapsToDomain (fse_F (n := n) q)) ∧
      ¬ fse_SinglePeaked fse_q0 0 ∧ ¬ fse_Dictatorship (fse_F (n := n) fse_q0) ∧
      fse_Anonymous (fse_F (n := n) fse_q0) := by
  have hF0 : fse_F (n := n) fse_q0 = fse_leftmost := by
    funext x; simp [fse_F, fse_q0_antitone]
  refine ⟨fun q hq => ?_, fse_q0_not_singlePeaked, ?_, ?_⟩
  · have hpos : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ q y := fun y hy => le_of_lt (hq.2 y hy)
    by_cases ha : AntitoneOn q (Set.Icc 0 1)
    · have hF : fse_F (n := n) q = fse_leftmost := by funext x; simp [fse_F, ha]
      rw [hF]
      exact ⟨fse_leftmost_SP_of_antitone q ha hpos, fse_leftmost_surjective, fse_leftmost_mapsTo⟩
    · have hF : fse_F (n := n) q = fun x => x 0 := by funext x; simp [fse_F, ha]
      rw [hF]
      refine ⟨fse_dictator_SP q hpos 0, fun y hy => ⟨fun _ => y, fun _ => hy, rfl⟩,
        fun x hx => hx 0⟩
  · rw [hF0]; exact fse_leftmost_not_dictatorship hn
  · rw [hF0]; exact fse_leftmost_anonymous
