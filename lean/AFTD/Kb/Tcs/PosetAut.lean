import AFTD.Prelude

/-!
# poset_aut

Topic: combinatorics   Node: b21fd4f8fe59

Provenance: formalization of a published result. Source: arXiv:2611.15540 Section 1

The automorphism group of a partially ordered set P is the subgroup of permutations σ of P preserving the partial order in both directions.
-/

/-- The automorphism group Aut(P) of a partially ordered set P as a subgroup of Equiv.Perm P. -/
def poset_aut (P : Type*) [PartialOrder P] : Subgroup (Equiv.Perm P) where
  carrier := { σ : Equiv.Perm P | ∀ x y : P, x ≤ y ↔ σ x ≤ σ y }
  mul_mem' := by
    intro a b ha hb x y
    exact (hb x y).trans (ha (b x) (b y))
  one_mem' := by
    intro x y
    rfl
  inv_mem' := by
    intro a ha x y
    dsimp at ha ⊢
    have h := (ha (a.symm x) (a.symm y)).symm
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h
