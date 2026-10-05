import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TfxAlphaEFXAt

/-!
# tfx_alphaTEFX

Topic: fair_division   Node: 6ba210e0f5f3

α-TEFX: the cumulative allocation is α-EFX after every round.
-/

/-- `α`-TEFX: the cumulative allocation is `α`-EFX after every round. -/
def tfx_alphaTEFX {T m : ℕ} (α : ℝ) (v : Fin 2 → Fin m → ℝ) (σ : Fin T → Fin m → Fin 2) :
    Prop :=
  ∀ t : ℕ, t < T → tfx_alphaEFXAt α v σ t
