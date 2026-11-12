import AFTD.Prelude
import AFTD.Kb.Tcs.CoordPermMulAction
import AFTD.Kb.Tcs.QuotientPosetPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# coordinate_orbit_invariant_orderhom_iso

Topic: combinatorics   Node: 156462be19c5

Provenance: helper lemma. arXiv:2611.13887, Lemma 8

For a subgroup of coordinate permutations of the n-fold product of the finite chain Fin m and a partially ordered set T, the pointwise ordered invariant monotone maps into T are order-isomorphic to the monotone maps from the orbit quotient with the representative-comparison preorder into T.
-/

open scoped Classical

theorem coordinate_orbit_invariant_orderhom_iso (n m : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) (T : Type*) [PartialOrder T] : letI : MulAction G (Fin n → Fin m) := coord_perm_mul_action G; letI : Preorder (MulAction.orbitRel.Quotient G (Fin n → Fin m)) := quotient_poset_preorder n (Fin m) G; Nonempty ({f : (Fin n → Fin m) →o T // ∀ (g : G) (x : Fin n → Fin m), f (g • x) = f x} ≃o (MulAction.orbitRel.Quotient G (Fin n → Fin m) →o T)) := by
  letI : MulAction G (Fin n → Fin m) := coord_perm_mul_action G
  letI : Preorder (MulAction.orbitRel.Quotient G (Fin n → Fin m)) := quotient_poset_preorder n (Fin m) G
  let R := MulAction.orbitRel G (Fin n → Fin m)
  have hmk : ∀ x y : Fin n → Fin m, x ≤ y →
      @LE.le (MulAction.orbitRel.Quotient G (Fin n → Fin m)) (quotient_poset_preorder n (Fin m) G).toLE
        (Quotient.mk R x) (Quotient.mk R y) :=
    fun x y h => ⟨x, y, rfl, rfl, h⟩
  let toQ : {f : (Fin n → Fin m) →o T // ∀ (g : G) (x : Fin n → Fin m), f (g • x) = f x} →
      (MulAction.orbitRel.Quotient G (Fin n → Fin m) →o T) := fun f =>
    { toFun := Quotient.lift f.1 (by
        rintro a b ⟨g, rfl⟩
        exact f.2 g b)
      monotone' := by
        rintro a b ⟨x, y, rfl, rfl, hxy⟩
        exact f.1.monotone hxy }
  let ofQ : (MulAction.orbitRel.Quotient G (Fin n → Fin m) →o T) →
      {f : (Fin n → Fin m) →o T // ∀ (g : G) (x : Fin n → Fin m), f (g • x) = f x} := fun F =>
    ⟨{ toFun := fun x => F (Quotient.mk R x)
       monotone' := fun x y h => F.monotone (hmk x y h) },
     fun g x => by
       show F (Quotient.mk R (g • x)) = F (Quotient.mk R x)
       congr 1
       exact Quotient.sound ⟨g, rfl⟩⟩
  refine ⟨{ toFun := toQ, invFun := ofQ, left_inv := ?_, right_inv := ?_, map_rel_iff' := ?_ }⟩
  · intro f
    rfl
  · intro F
    ext a
    induction a using Quotient.inductionOn with
    | h x => rfl
  · intro f g
    constructor
    · intro h x
      exact h (Quotient.mk R x)
    · intro h a
      induction a using Quotient.inductionOn with
      | h x => exact h x
