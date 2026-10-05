import AFTD.Prelude

/-!
# fse_IsScaling

Topic: mechanism_design   Node: 4a68059468ac

A scaling function in the sense of arXiv 2402.18908: continuous and positive on [0,1].
-/

/-- A scaling function in the sense of arXiv 2402.18908: continuous and positive on `[0,1]`. -/
def fse_IsScaling (q : ℝ → ℝ) : Prop :=
  ContinuousOn q (Set.Icc 0 1) ∧ ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < q y
