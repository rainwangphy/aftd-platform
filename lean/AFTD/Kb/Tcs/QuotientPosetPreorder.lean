import AFTD.Prelude
import AFTD.Kb.Tcs.CoordPermMulAction

/-!
# quotient_poset_preorder

Topic: combinatorics   Node: a004f0298eda

Provenance: formalization of a published result. Source: arXiv:2611.13887 Section 3

The preorder on the quotient poset of orbits of P^n under a subgroup G of S_n acting by coordinate permutations, where orbit Gx is less than or equal to orbit Gy if and only if there exist representatives x' in Gx and y' in Gy such that x' is less than or equal to y' in the product order on P^n.
-/

/-- The preorder on the orbit quotient of Fin n → P under the coordinate permutation action of G, where Gx ≤ Gy iff there exist x' in Gx, y' in Gy with x' ≤ y'. -/
instance quotient_poset_preorder (n : ℕ) (P : Type*) [Preorder P]
    (G : Subgroup (Equiv.Perm (Fin n))) :
    Preorder (MulAction.orbitRel.Quotient G (Fin n → P)) where
  le a b := ∃ (x y : Fin n → P), Quotient.mk (MulAction.orbitRel G (Fin n → P)) x = a ∧
                       Quotient.mk (MulAction.orbitRel G (Fin n → P)) y = b ∧ x ≤ y
  lt a b := (∃ (x y : Fin n → P), Quotient.mk (MulAction.orbitRel G (Fin n → P)) x = a ∧
                       Quotient.mk (MulAction.orbitRel G (Fin n → P)) y = b ∧ x ≤ y) ∧
            ¬(∃ (x y : Fin n → P), Quotient.mk (MulAction.orbitRel G (Fin n → P)) x = b ∧
                       Quotient.mk (MulAction.orbitRel G (Fin n → P)) y = a ∧ x ≤ y)
  le_refl a := by
    induction a using Quotient.inductionOn with
    | h x => exact ⟨x, x, rfl, rfl, le_rfl⟩
  le_trans a b c hab hbc := by
    rcases hab with ⟨x, y, hx, hy, hxy⟩
    rcases hbc with ⟨y', z, hy', hz, hy'z⟩
    have hyy' : (MulAction.orbitRel G (Fin n → P)).r y y' := by
      rw [← Quotient.eq, hy, hy']
    rcases hyy' with ⟨g, hg⟩
    dsimp at hg
    have hg_le : g⁻¹ • x ≤ g⁻¹ • y := fun i => hxy (g⁻¹.1⁻¹ i)
    have h_eq : g⁻¹ • y = y' := by rw [← hg, inv_smul_smul]
    rw [h_eq] at hg_le
    refine ⟨g⁻¹ • x, z, ?_, hz, le_trans hg_le hy'z⟩
    rw [← hx]
    exact Quotient.sound ⟨g⁻¹, rfl⟩
  lt_iff_le_not_ge _ _ := Iff.rfl
