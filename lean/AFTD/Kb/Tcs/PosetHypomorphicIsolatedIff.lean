import AFTD.Prelude
import AFTD.Kb.Tcs.PosetHypomorphic
import AFTD.Kb.Tcs.PosetHypomorphicCardLtPairsEq
import AFTD.Kb.Tcs.PosetDeleteIsolatedLtPairCountIff
import AFTD.Kb.Tcs.PosetLtPairCountEqOfOrderIso
import AFTD.Kb.Tcs.PosetLtPairCount

/-!
# poset_hypomorphic_isolated_iff

Topic: combinatorics   Node: 3c078c60aac3

Provenance: helper lemma. step towards poset_height_one_reconstructible

Let finite ordered sets P, Q have |P| ≥ 3 and the same deck, witnessed by the bijection σ with P − x ≅ Q − σ(x) for all x. Then for every x ∈ P, x is incomparable with everything in P if and only if σ(x) is incomparable with everything in Q. In particular the isolated points of P correspond exactly to those of Q.
-/

/-- A deck bijection carries isolated points to isolated points (both directions). -/
theorem poset_hypomorphic_isolated_iff (P Q : Type) [Fintype P] [Fintype Q] [PartialOrder P] [PartialOrder Q] (hn : 3 ≤ Fintype.card P) (σ : P ≃ Q) (hσ : ∀ x : P, Nonempty ({y : P // y ≠ x} ≃o {y : Q // y ≠ σ x})) (x : P) : (∀ y : P, ¬ (x < y ∨ y < x)) ↔ (∀ z : Q, ¬ (σ x < z ∨ z < σ x)) := by
  classical
  have h_count_PQ : poset_lt_pair_count P = poset_lt_pair_count Q := by
    have hP : poset_lt_pair_count P = (Finset.univ.filter (fun p : P × P => p.1 < p.2)).card := by
      unfold poset_lt_pair_count
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hQ : poset_lt_pair_count Q = (Finset.univ.filter (fun p : Q × Q => p.1 < p.2)).card := by
      unfold poset_lt_pair_count
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hP, hQ]
    exact poset_hypomorphic_card_lt_pairs_eq P Q hn ⟨σ, hσ⟩
  have h_iso_count : poset_lt_pair_count {y : P // y ≠ x} = poset_lt_pair_count {y : Q // y ≠ σ x} := by
    obtain ⟨e⟩ := hσ x
    exact poset_lt_pair_count_eq_of_order_iso _ _ e
  rw [← poset_delete_isolated_lt_pair_count_iff P x]
  rw [← poset_delete_isolated_lt_pair_count_iff Q (σ x)]
  rw [h_iso_count, h_count_PQ]
