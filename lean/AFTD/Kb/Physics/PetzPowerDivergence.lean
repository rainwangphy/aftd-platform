import AFTD.Prelude

/-!
# petz_power_divergence

Topic: quantum_mechanics   Node: bde0451da60e

Provenance: formalization of a published result. Source: OP-1440

The Petz power divergence petz_power_divergence β ρ σ of type ℝ for an exponent β : ℝ and real matrices ρ, σ : Matrix n n ℝ on a finite type n with decidable equality, defined as (1 - (cfc (fun x : ℝ => x ^ β) ρ * cfc (fun x : ℝ => x ^ (1 - β)) σ).trace) / (β * (1 - β)).
-/

/-- The Petz power divergence D_beta(rho || sigma) for real matrices. -/
noncomputable def petz_power_divergence {n : Type*} [Fintype n] [DecidableEq n]
    (β : ℝ) (ρ σ : Matrix n n ℝ) : ℝ := (1 - (cfc (fun x : ℝ => x ^ β) ρ * cfc (fun x : ℝ => x ^ (1 - β)) σ).trace) / (β * (1 - β))
