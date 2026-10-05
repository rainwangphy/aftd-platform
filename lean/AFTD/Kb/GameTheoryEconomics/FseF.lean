import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseLeftmost

/-!
# fse_F

Topic: mechanism_design   Node: edfbab8b7748

The q-dependent mechanism used for the refutation in the model where the mechanism also receives the scaling function: the leftmost mechanism when q is non-increasing on [0,1], and agent 0's dictatorship otherwise.
-/

/-- The `q`-dependent mechanism used for the refutation in the model where the mechanism also receives the scaling function: the leftmost mechanism when `q` is non-increasing on `[0,1]`, and agent `0`'s dictatorship otherwise. -/
noncomputable def fse_F {n : ℕ} [NeZero n] (q : ℝ → ℝ) (x : Fin n → ℝ) : ℝ := by
  classical
  exact if AntitoneOn q (Set.Icc 0 1) then fse_leftmost x else x 0
