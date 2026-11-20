import AFTD.Prelude

/-!
# plane_power_coord_change

Topic: combinatorics   Node: ff35f6f8471c

Provenance: formalization of a published result. Source: arXiv:2611.20408, Lemma 2.2 proof

The coordinate change map $\sigma : (\mathbb{F}_3^2)^n \to \mathbb{F}_3^n \times \mathbb{F}_3^n$ given by $((s_j, t_j))_{j=0}^{n-1} \mapsto ((s_j - t_j)_{j=0}^{n-1}, (s_j)_{j=0}^{n-1})$ is a linear isomorphism of $\mathbb{F}_3$-modules.
-/

/-- The linear coordinate change $\sigma : (\mathbb{F}_3^2)^n \simeq \mathbb{F}_3^n \times \mathbb{F}_3^n$ sending $(s_j, t_j)$ to $((s_j - t_j), (s_j))$. -/
def plane_power_coord_change (n : ℕ) :
    (Fin n → ZMod 3 × ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3) × (Fin n → ZMod 3) := by
  refine {
    toFun := fun ξ => (fun j => (ξ j).1 - (ξ j).2, fun j => (ξ j).1)
    invFun := fun p j => (p.2 j, p.2 j - p.1 j)
    left_inv := fun ξ => by ext j <;> simp
    right_inv := fun p => by ext j <;> simp
    map_add' := fun x y => by ext j <;> simp <;> ring
    map_smul' := fun c x => by ext j <;> simp <;> ring
  }
