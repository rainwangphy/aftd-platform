import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TfxBval

/-!
# tfx_alphaEFXAt

Topic: fair_division   Node: a52e8a83a205

α-EFX of the cumulative allocation after round t: for all agents i ≠ j and every good (copy of type g from round s ≤ t) in j's bundle, v_i(A_i) ≥ α · v_i(A_j \ {that good}).
-/

/-- `α`-EFX of the cumulative allocation after round `t`: for all agents `i ≠ j` and every good (copy of type `g` from round `s ≤ t`) in `j`'s bundle, `v_i(A_i) ≥ α · v_i(A_j \ {that good})`. -/
def tfx_alphaEFXAt {T m : ℕ} (α : ℝ) (v : Fin 2 → Fin m → ℝ) (σ : Fin T → Fin m → Fin 2)
    (t : ℕ) : Prop :=
  ∀ i j : Fin 2, i ≠ j → ∀ (s : Fin T) (g : Fin m), s.val ≤ t → σ s g = j →
    α * (tfx_bval v σ t i j - v i g) ≤ tfx_bval v σ t i i
