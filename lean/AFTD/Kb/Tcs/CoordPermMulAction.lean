import AFTD.Prelude

/-!
# coord_perm_mul_action

Topic: combinatorics   Node: 58cc3ab36e2a

Provenance: formalization of a published result. Source: arXiv:2611.13887, Section 3

A subgroup of the symmetric group on n elements acts on functions from Fin n to any type by permuting coordinates: (g • x) i = x (g⁻¹ i).
-/

/-- Coordinate permutation action of a subgroup of the symmetric group on functions from Fin n. -/
instance coord_perm_mul_action {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n))) {α : Type*} :
    MulAction G (Fin n → α) := {
  smul := fun g x i => x (g.1⁻¹ i)
  one_smul := fun x => by
    ext i
    change x ((1 : G).1⁻¹ i) = x i
    simp
  mul_smul := fun g h x => by
    ext i
    change x ((g * h).1⁻¹ i) = x (h.1⁻¹ (g.1⁻¹ i))
    simp
}
