import AFTD.Prelude

/-!
# tsallis_exposure

Topic: mechanism_design   Node: f995eb85b2da

The Tsallis exposure (gradient of the expected reward): gamma x_k^(gamma - 1).
-/

def tsallis_exposure {n : ℕ} (γ : ℕ) (x : Fin n → ℝ) (k : Fin n) : ℝ :=
  γ * x k ^ (γ - 1)
