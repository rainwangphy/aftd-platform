import AFTD.Prelude
import AFTD.Kb.Tcs.CoordPermMulAction
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# pgroup_coordinate_invariant_orderhom_card_mod

Topic: combinatorics   Node: fdb848b8784a

Provenance: helper lemma. arXiv:2611.13887, Lemma 4 applied in Lemma 9

For prime p and a p-subgroup of the coordinate-permutation group, the number of monotone maps from the n-fold product of the finite chain Fin m to a finite poset is congruent modulo p to the number of those maps invariant under the group.
-/

open scoped Classical

theorem pgroup_coordinate_invariant_orderhom_card_mod (p n m : ℕ) (hp : p.Prime) (G : Subgroup (Equiv.Perm (Fin n))) (hG : IsPGroup p G) (T : Type*) [Fintype T] [PartialOrder T] : letI : MulAction G (Fin n → Fin m) := coord_perm_mul_action G; Nat.ModEq p (Nat.card ((Fin n → Fin m) →o T)) (Nat.card {f : (Fin n → Fin m) →o T // ∀ (g : G) (x : Fin n → Fin m), f (g • x) = f x}) := by
  letI : MulAction G (Fin n → Fin m) := coord_perm_mul_action G
  haveI : Fact p.Prime := ⟨hp⟩
  have hsmul : ∀ (g : G) (x : Fin n → Fin m) (i : Fin n), (g • x) i = x (g.1⁻¹ i) :=
    fun _ _ _ => rfl
  have hmono : ∀ g : G, Monotone (fun x : Fin n → Fin m => g • x) := by
    intro g x y h i
    show x (g.1⁻¹ i) ≤ y (g.1⁻¹ i)
    exact h _
  letI act : MulAction G ((Fin n → Fin m) →o T) :=
    { smul := fun g f => ⟨fun x => f (g⁻¹ • x), fun x y h => f.monotone (hmono g⁻¹ h)⟩
      one_smul := fun f => by
        ext x
        show f ((1 : G)⁻¹ • x) = f x
        simp
      mul_smul := fun g h f => by
        ext x
        show f ((g * h)⁻¹ • x) = f (h⁻¹ • (g⁻¹ • x))
        rw [mul_inv_rev, mul_smul] }
  have hfin : Finite ((Fin n → Fin m) →o T) :=
    Finite.of_injective (fun f : (Fin n → Fin m) →o T => (f : (Fin n → Fin m) → T))
      DFunLike.coe_injective
  have key := hG.card_modEq_card_fixedPoints ((Fin n → Fin m) →o T)
  refine key.trans ?_
  unfold Nat.ModEq
  congr 1
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight ?_
  intro f
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro h g x
    have := DFunLike.congr_fun (h g⁻¹) x
    change f (g⁻¹⁻¹ • x) = f x at this
    simpa using this
  · intro h g
    ext x
    exact h g⁻¹ x
