import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsOnlineAlgorithm
import AFTD.Kb.GameTheoryEconomics.IsConsistentAlgorithm
import AFTD.Kb.GameTheoryEconomics.GuaranteesAlphaEefx

/-!
# has_consistent_eefx_algorithm

Topic: fair_division   Node: 97a11c88ffea

Provenance: formalization of a published result. Source: arXiv:2610.34625 Sec. 6.2

There exists an online, consistent algorithm alg for n agents and a positive constant α > 0 such that alg guarantees α-EEFX under error factor ρ.
-/

/-- There exists a consistent online algorithm guaranteeing alpha-EEFX for some alpha > 0 under error factor rho. -/
def has_consistent_eefx_algorithm (n : ℕ) (ρ : ℝ) : Prop :=
  ∃ (alg : ∀ m : ℕ, (Fin n → Fin m → ℝ) → (Fin n → Fin m → ℝ) → (Fin m → Fin n)) (α : ℝ),
    0 < α ∧ is_online_algorithm n alg ∧ is_consistent_algorithm n alg ∧ guarantees_alpha_eefx n alg ρ α
