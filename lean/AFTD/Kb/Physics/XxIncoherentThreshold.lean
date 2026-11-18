import AFTD.Prelude
import AFTD.Kb.Physics.XxInteractionHamiltonian

/-!
# xx_incoherent_threshold

Topic: quantum_mechanics   Node: f5815f718b29

Provenance: formalization of a published result. Source: arXiv:2611.05010, Yang et al., "Ergotropy Activation and Coherence in Dissipatively Charged Quantum Batteries", Section VI

For an open XX spin chain of length n at inverse temperature beta > 0, xx_incoherent_threshold n beta is the infimum of couplings g > 0 such that the incoherent ergotropy of the dephased thermal state Delta(rho_n(beta, g)) with respect to the bare Hamiltonian H_0 = sum_i Z_i is strictly positive, where Delta projects onto the computational Z-basis diagonal.
-/

/-- Incoherent ergotropy activation threshold c_inc(n, beta) for an open XX spin chain of length n at inverse temperature beta. -/
noncomputable def xx_incoherent_threshold (n : ℕ) (β : ℝ) : ℝ := letI : NormedRing (Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := Matrix.linftyOpNormedRing
  let H0 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
    Matrix.diagonal fun s => (∑ i : Fin n, if s i then (1 : ℂ) else (-1 : ℂ))
  let dephase (M : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
    Matrix.diagonal fun s => M s s
  let W (σ : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) : ℝ :=
    (Matrix.trace (H0 * σ)).re -
      sInf { (Matrix.trace (H0 * (U * σ * star U))).re |
        (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (_ : U ∈ Matrix.unitaryGroup (Fin n → Bool) ℂ) }
  let rho (g : ℝ) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
    let H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ := H0 + (g : ℂ) • xx_interaction_hamiltonian n
    let expH := NormedSpace.exp ((-β : ℂ) • H)
    (Matrix.trace expH)⁻¹ • expH
  sInf { g : ℝ | 0 < g ∧ 0 < W (dephase (rho g)) }
