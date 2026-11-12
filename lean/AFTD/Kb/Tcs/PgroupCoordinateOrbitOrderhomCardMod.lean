import AFTD.Prelude
import AFTD.Kb.Tcs.CoordPermMulAction
import AFTD.Kb.Tcs.QuotientPosetPreorder
import AFTD.Kb.Tcs.CoordinateOrbitInvariantOrderhomIso
import AFTD.Kb.Tcs.PgroupCoordinateInvariantOrderhomCardMod
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# pgroup_coordinate_orbit_orderhom_card_mod

Topic: combinatorics   Node: f0129e23a7eb

Provenance: formalization of a published result. Source: arXiv:2611.13887, Lemma 9; finite target poset

Let p be prime, G a p-subgroup of the permutations of Fin n acting by coordinate permutations on the n-fold product of the finite chain Fin m, and T a finite partially ordered set. The number of monotone maps from that product to T is congruent modulo p to the number of monotone maps from its orbit quotient, ordered by comparison of representatives, to T.
-/

open scoped Classical

theorem pgroup_coordinate_orbit_orderhom_card_mod (p n m : ℕ) (hp : p.Prime) (G : Subgroup (Equiv.Perm (Fin n))) (hG : IsPGroup p G) (T : Type*) [Fintype T] [PartialOrder T] : letI : MulAction G (Fin n → Fin m) := coord_perm_mul_action G; letI : Preorder (MulAction.orbitRel.Quotient G (Fin n → Fin m)) := quotient_poset_preorder n (Fin m) G; Nat.ModEq p (Nat.card ((Fin n → Fin m) →o T)) (Nat.card (MulAction.orbitRel.Quotient G (Fin n → Fin m) →o T)) := by
  letI : MulAction G (Fin n → Fin m) := coord_perm_mul_action G
  letI : Preorder (MulAction.orbitRel.Quotient G (Fin n → Fin m)) := quotient_poset_preorder n (Fin m) G
  obtain ⟨e⟩ := coordinate_orbit_invariant_orderhom_iso n m G T
  exact (pgroup_coordinate_invariant_orderhom_card_mod p n m hp G hG T).trans
    (by rw [Nat.card_congr e.toEquiv])
