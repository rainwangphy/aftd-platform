import AFTD.Prelude

/-!
# is_t_spaced_word

Topic: information   Node: 8993def22129

Provenance: formalization of a published result. Source: knowledgebase, OP-1503

A word y : Fin n → Fin q is t-spaced if y i ≠ y j for all indices i, j : Fin n satisfying i.val < j.val and j.val ≤ i.val + t.
-/

/-- Property that a q-ary word has distinct symbols at all pairs of indices within distance at most t. -/
def is_t_spaced_word (t : ℕ) {n q : ℕ} (y : Fin n → Fin q) : Prop := ∀ (i j : Fin n), i.val < j.val → j.val ≤ i.val + t → y i ≠ y j
