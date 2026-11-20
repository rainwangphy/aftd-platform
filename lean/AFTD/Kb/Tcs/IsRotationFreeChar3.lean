import AFTD.Prelude
import AFTD.Kb.Tcs.PlaneChar3RotationMap

/-!
# is_rotation_free_char3

Topic: combinatorics   Node: 8272eaee2baa

Provenance: formalization of a published result. Source: arXiv:2611.20408, Section 2.2

A finite subset $S$ of $(\mathbb{F}_3^2)^n$ is rotation-free if for all $\xi, \eta, \zeta \in S$, $\zeta = (I_{2n} - \mathcal{R})\xi + \mathcal{R}\eta$ implies $\xi = \eta$ and $\eta = \zeta$.
-/

/-- Predicate for a finite subset $S \subseteq (\mathbb{F}_3^2)^n$ to be rotation-free with respect to $\mathcal{R}$. -/
def is_rotation_free_char3 (n : ℕ) (S : Finset (Fin n → ZMod 3 × ZMod 3)) : Prop :=
  ∀ ⦃ξ⦄, ξ ∈ S → ∀ ⦃η⦄, η ∈ S → ∀ ⦃ζ⦄, ζ ∈ S →
    ζ = (1 - plane_char3_rotation_map n) ξ + plane_char3_rotation_map n η →
      ξ = η ∧ η = ζ
