import AFTD.Prelude
import AFTD.Kb.Tcs.PosetLtPairCount

/-!
# poset_lt_pair_count_eq_of_order_iso

Topic: combinatorics   Node: 246cc6c65469

Provenance: helper lemma. step towards poset_height_one_reconstructible

Order-isomorphic ordered sets have the same number of comparable pairs.
-/

/-- `poset_lt_pair_count` is an invariant of order isomorphism. -/
theorem poset_lt_pair_count_eq_of_order_iso (P Q : Type) [Fintype P] [Fintype Q] [PartialOrder P] [PartialOrder Q] (e : P ≃o Q) : poset_lt_pair_count P = poset_lt_pair_count Q := by
  unfold poset_lt_pair_count
  exact Nat.card_congr (Equiv.subtypeEquiv (e.toEquiv.prodCongr e.toEquiv) (fun a => by
    show a.1 < a.2 ↔ e a.1 < e a.2
    exact e.lt_iff_lt.symm))
