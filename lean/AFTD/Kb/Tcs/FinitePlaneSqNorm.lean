import AFTD.Prelude

/-!
# finite_plane_sq_norm

Topic: combinatorics   Node: 05b0ff84dd3f

Provenance: formalization of a published result. Source: arXiv:2611.20408, Section 1

The squared norm of a vector $(a, b) \in \mathbb{F}_p^2$ is defined as $\|(a, b)\|^2 = a^2 + b^2$.
-/

/-- Squared Euclidean norm of a vector in (ZMod p)^2. -/
def finite_plane_sq_norm {p : ℕ} (v : ZMod p × ZMod p) : ZMod p := v.1 ^ 2 + v.2 ^ 2
