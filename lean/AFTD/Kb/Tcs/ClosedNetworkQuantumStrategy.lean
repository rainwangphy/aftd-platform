import AFTD.Prelude
import AFTD.Kb.Tcs.IsDichotomicObservable

/-!
# ClosedNetworkQuantumStrategy

Topic: quantum   Node: f4d71cd116ab

Provenance: formalization of a published result. Source: arXiv:2610.35838 Sec. VI

For a natural number n and a complex Hilbert space H, a quantum measurement strategy ClosedNetworkQuantumStrategy n H on H consists of a unit state vector ψ in H with ‖ψ‖ = 1, two bounded self-adjoint continuous linear operators F₀, F₁ on H with operator norm at most 1, and for each end node i in Fin n and setting y in Fin 2, a dichotomic projective observable B i y on H, such that B i y and B j y' commute for distinct nodes i ≠ j, and F₀ and F₁ commute with all B i y.
-/

/-- A quantum measurement strategy in the closed network on a given Hilbert space H with n end nodes. -/
structure ClosedNetworkQuantumStrategy (n : ℕ) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  ψ : H
  hψ : ‖ψ‖ = 1
  F₀ : H →L[ℂ] H
  F₁ : H →L[ℂ] H
  hF₀_sa : IsSelfAdjoint F₀
  hF₁_sa : IsSelfAdjoint F₁
  hF₀_norm : ‖F₀‖ ≤ 1
  hF₁_norm : ‖F₁‖ ≤ 1
  B : Fin n → Fin 2 → (H →L[ℂ] H)
  hB_dichotomic : ∀ i y, is_dichotomic_observable (B i y)
  hB_comm : ∀ (i j : Fin n) (y y' : Fin 2), i ≠ j → B i y * B j y' = B j y' * B i y
  hFB₀ : ∀ (i : Fin n) (y : Fin 2), F₀ * B i y = B i y * F₀
  hFB₁ : ∀ (i : Fin n) (y : Fin 2), F₁ * B i y = B i y * F₁
