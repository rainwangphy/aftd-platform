import AFTD.Prelude
import AFTD.Kb.Tcs.PermCoordSmul

/-!
# perm_coord_mul_action

Topic: combinatorics   Node: c78b5823240a

Provenance: formalization of a published result. Source: scout/2611-13887-congruences-for-dedekind-numbers.md:228

Permutations of coordinates define a group action of the symmetric group on the Cartesian product P^n.
-/

/-- The group action of Equiv.Perm (Fin n) on Fin n → P by permutation of coordinates. -/
instance perm_coord_mul_action (n : ℕ) (P : Type*) : MulAction (Equiv.Perm (Fin n)) (Fin n → P) := {
  smul := perm_coord_smul n P
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
}
