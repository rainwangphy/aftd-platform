import AFTD.Prelude

/-!
# is_word_run

Topic: information   Node: 4f567c8c1896

Provenance: original. Related work: folklore

A pair of indices 0 ≤ a < b ≤ n forms a run [a, b) of a word y : Fin n → α if all symbols y i for a ≤ i < b are equal, and the block cannot be extended to the left (a = 0 or y(a - 1) ≠ y a) or to the right (b = n or y b ≠ y a).
-/

/-- A contiguous block [a, b) of indices is a run of word y : Fin n → α if all letters in [a, b) are equal and it cannot be extended to the left or right. -/
def is_word_run {n : ℕ} {α : Type*} (y : Fin n → α) (a b : ℕ) : Prop := ∃ (hab : a < b) (hbn : b ≤ n),
    (∀ (i : Fin n), a ≤ i.val ∧ i.val < b → y i = y ⟨a, hab.trans_le hbn⟩) ∧
    (a = 0 ∨ ∃ (ha : 0 < a), y ⟨a - 1, by omega⟩ ≠ y ⟨a, hab.trans_le hbn⟩) ∧
    (b = n ∨ ∃ (hb : b < n), y ⟨b, hb⟩ ≠ y ⟨a, hab.trans_le hbn⟩)
