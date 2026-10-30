import AFTD.Prelude

/-!
# wild_involutions_conjugate_of_fixed_count

Topic: graphs   Node: 4e0616efacdf

Provenance: helper lemma. IN-382 / OP-306 campaign9, 2026-10-30. Standard finite involution conjugacy and permutation transport, supporting the moment route for https://arxiv.org/html/2610.22142v1. Background https://arxiv.org/abs/0911.3604 . No new wild-number bound or research advance is claimed.

For two involutive permutations of any finite type, equality of the numbers of fixed points implies that a permutation simultaneously carries every f-edge to a g-edge.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

theorem wild_involutions_conjugate_of_fixed_count
    {V : Type*} [Fintype V] [DecidableEq V]
    (f g : Equiv.Perm V)
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (hcard : (univ.filter fun x => f x = x).card =
      (univ.filter fun x => g x = x).card) :
    ∃ e : Equiv.Perm V, ∀ x, e (f x) = g (e x) := by
  have hf2 : f ^ 2 = 1 := by ext x; exact hf x
  have hg2 : g ^ 2 = 1 := by ext x; exact hg x
  have hfs := Equiv.Perm.cycleType_of_pow_prime_eq_one hf2
  have hgs := Equiv.Perm.cycleType_of_pow_prime_eq_one hg2
  have hc : f.support.card = g.support.card := by
    have he (a : Equiv.Perm V) :
        a.support = univ \ (univ.filter fun x => a x = x) := by
      ext x
      simp
    rw [he f, he g, card_sdiff_of_subset (subset_univ _),
      card_sdiff_of_subset (subset_univ _), hcard]
  have hsf : f.support.card = f.cycleType.card * 2 := by
    rw [← f.sum_cycleType]
    conv_lhs => rw [hfs]
    simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id]
  have hsg : g.support.card = g.cycleType.card * 2 := by
    rw [← g.sum_cycleType]
    conv_lhs => rw [hgs]
    simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id]
  have hs : f.cycleType.card * 2 = g.cycleType.card * 2 := by omega
  have hlen : f.cycleType.card = g.cycleType.card := by omega
  have htype : f.cycleType = g.cycleType :=
    hfs.trans ((congrArg (fun k => Multiset.replicate k 2) hlen).trans hgs.symm)
  obtain ⟨e, he⟩ := isConj_iff.mp (Equiv.Perm.isConj_of_cycleType_eq htype)
  refine ⟨e, ?_⟩
  intro x
  have hh := congrArg (fun a : Equiv.Perm V => a (e x)) he
  simpa using hh
