import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OrderPrefix
import AFTD.Kb.Tcs.IntegerBoxCompletionCardLe

/-!
# order_prefix_zero

Topic: general_equilibrium   Node: b435145647dc

Provenance: helper lemma. arXiv:2611.16207, Lemma 2

For any ordering bijection e of a finite type α, the prefix of length zero is empty: order_prefix e 0 = ∅.
-/

/-- The prefix of length zero of any ordering bijection is the empty set. -/
theorem order_prefix_zero {α : Type*} [DecidableEq α] [Fintype α]
    (e : Fin (Fintype.card α) ≃ α) :
    order_prefix e 0 = ∅ := by first | exact integer_box_completion_card_le | (apply integer_box_completion_card_le <;> assumption) | (apply integer_box_completion_card_le <;> simp_all) | simpa using integer_box_completion_card_le | (simp only [order_prefix] at *; first | exact integer_box_completion_card_le | (apply integer_box_completion_card_le <;> assumption) | (apply integer_box_completion_card_le <;> simp_all) | simpa using integer_box_completion_card_le)
