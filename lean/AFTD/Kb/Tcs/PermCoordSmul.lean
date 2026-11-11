import AFTD.Prelude

/-!
# perm_coord_smul

Topic: combinatorics   Node: 8dc2f7cac0d2

Provenance: formalization of a published result. Source: scout/2611-13887-congruences-for-dedekind-numbers.md:228

Given a permutation σ of Fin n and a vector x : Fin n → P, the permuted vector has i-th component x(σ⁻¹(i)).
-/

/-- The coordinate permutation action of Equiv.Perm (Fin n) on Fin n → P. -/
def perm_coord_smul (n : ℕ) (P : Type*) (σ : Equiv.Perm (Fin n)) (x : Fin n → P) : Fin n → P := fun i => x (σ.symm i)
