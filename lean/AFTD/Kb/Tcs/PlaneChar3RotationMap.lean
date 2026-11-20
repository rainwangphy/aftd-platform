import AFTD.Prelude

/-!
# plane_char3_rotation_map

Topic: combinatorics   Node: 93e282b251b8

Provenance: formalization of a published result. Source: arXiv:2611.20408, Section 2.2

Let $n \ge 0$. The linear endomorphism $\mathcal{R}$ on $(\mathbb{F}_3^2)^n$ is defined coordinate-wise by $(s_j, t_j) \mapsto (-t_j, s_j + t_j)$ for all $j \in \{0, \dots, n-1\}$.
-/

/-- Coordinate-wise rotation linear map $\mathcal{R}$ on $(\mathbb{F}_3^2)^n$ mapping $(s_j, t_j)$ to $(-t_j, s_j + t_j)$. -/
def plane_char3_rotation_map (n : ℕ) :
    (Fin n → ZMod 3 × ZMod 3) →ₗ[ZMod 3] (Fin n → ZMod 3 × ZMod 3) := by
  refine {
    toFun := fun ξ j => (- (ξ j).2, (ξ j).1 + (ξ j).2)
    map_add' := fun x y => by ext j <;> simp <;> ring
    map_smul' := fun c x => by ext j <;> simp <;> ring
  }
