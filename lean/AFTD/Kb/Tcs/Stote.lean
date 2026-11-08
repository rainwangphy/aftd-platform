import AFTD.Prelude
import AFTD.Kb.Tcs.JordanProd

/-!
# stote

Topic: quantum   Node: 7cba600ed83e

Provenance: formalization of a published result. Source: arXiv:2610.34972 eq. (1)

For finite types dA and dB with decidable equality on dB, the state over time stote of a complex matrix ρ on dA and a complex matrix J on dA × dB is jordan_prod (Matrix.kronecker ρ (1 : Matrix dB dB ℂ)) J.
-/

/-- The state over time (stote) Q_{ρ, J} = (ρ ⊗ 1) ★ J. -/
noncomputable def stote {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
    (ρ : Matrix dA dA ℂ) (J : Matrix (dA × dB) (dA × dB) ℂ) :
    Matrix (dA × dB) (dA × dB) ℂ := jordan_prod (Matrix.kronecker ρ (1 : Matrix dB dB ℂ)) J
