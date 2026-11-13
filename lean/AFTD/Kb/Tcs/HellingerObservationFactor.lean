import AFTD.Prelude
import AFTD.Kb.Tcs.HellingerMutualInformation

/-!
# hellinger_observation_factor

Topic: information   Node: 025569f35dc8

Provenance: formalization of a published result. Source: arXiv:2610.21231 (On the Subadditivity of Mutual f-Information)

A real number C satisfies the m-observation multiplicative subadditivity inequality for Hellinger mutual information if for every finite type X and family of finite observation types Y_i (for i in Fin m), every prior distribution pX on X and conditionally independent channels P_i from X to Y_i, the joint Hellinger mutual information H(X; Y_1, ..., Y_m) is at most C times the sum of the individual Hellinger mutual informations sum_i H(X; Y_i).
-/

/-- Multiplicative factor for Hellinger mutual information with m conditionally independent observations -/
def hellinger_observation_factor (m : ℕ) (C : ℝ) : Prop := ∀ (X : Type) (Y : Fin m → Type) [Fintype X] [∀ i, Fintype (Y i)]
    (pX : X → ℝ) (P : ∀ i, X → Y i → ℝ),
    (∀ x, 0 ≤ pX x) → (∑ x, pX x = 1) →
    (∀ i x y, 0 ≤ P i x y) → (∀ i x, ∑ y, P i x y = 1) →
    hellinger_mutual_information (fun x (y : (i : Fin m) → Y i) => pX x * ∏ i, P i x (y i)) ≤
      C * ∑ i, hellinger_mutual_information (fun x y => pX x * P i x y)
