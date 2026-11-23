import AFTD.Prelude
import AFTD.Kb.Tcs.Biplane

/-!
# biplane_automorphism_group

Topic: combinatorics   Node: 59295a3f9955

Provenance: formalization of a published result. Source: arXiv:2611.17855, Section 2.2 and Proposition 2.11

The automorphism group of a biplane, defined as the subgroup of permutations of points and lines preserving incidence.
-/

/-- The automorphism group of a biplane. -/
def biplane_automorphism_group {P L : Type*} [Fintype P] [Fintype L] (B : Biplane P L) : Subgroup (Equiv.Perm P × Equiv.Perm L) where
  carrier := { g | ∀ p l, B.inc (g.1 p) (g.2 l) ↔ B.inc p l }
  mul_mem' {g h} hg hh p l := by dsimp at hg hh ⊢; rw [hg, hh]
  one_mem' p l := Iff.rfl
  inv_mem' {g} hg p l := by
    dsimp at hg ⊢
    have := (hg (g.1.symm p) (g.2.symm l)).symm
    rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
