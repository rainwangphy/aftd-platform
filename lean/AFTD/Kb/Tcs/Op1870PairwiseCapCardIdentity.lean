import AFTD.Prelude

/-!
# op_1870_pairwise_cap_card_identity

Topic: combinatorics   Node: b0cc174a6633

Provenance: helper lemma. arXiv:2611.19543 Lemma 4

For any three mutually disjoint finite sets $A_0, A_1, A_2$, the sum of the cardinalities of their pairwise unions satisfies $2 (|A_0| + |A_1| + |A_2|) = |A_0 \cup A_1| + |A_0 \cup A_2| + |A_1 \cup A_2|$.
-/

/-- The sum of cardinalities of pairwise unions of three mutually disjoint sets is twice their total cardinality. -/
theorem op_1870_pairwise_cap_card_identity {α : Type*} [DecidableEq α]
    (A₀ A₁ A₂ : Finset α)
    (h01 : Disjoint A₀ A₁) (h02 : Disjoint A₀ A₂) (h12 : Disjoint A₁ A₂) :
    2 * (A₀.card + A₁.card + A₂.card) =
      (A₀ ∪ A₁).card + (A₀ ∪ A₂).card + (A₁ ∪ A₂).card := by
  rw [Finset.card_union_of_disjoint h01, Finset.card_union_of_disjoint h02,
    Finset.card_union_of_disjoint h12]
  ring
