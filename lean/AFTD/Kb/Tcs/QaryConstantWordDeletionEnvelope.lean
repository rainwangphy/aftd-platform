import AFTD.Prelude

/-!
# qary_constant_word_deletion_envelope

Topic: information   Node: 863d57abd451

Provenance: formalization of a published result. Source: arXiv:2407.10026 "Conditional entropies of k-deletion/insertion channels"

For deletion radius t, alphabet size q, length n, and threshold r, the explicit upper envelope for the constant-word deletion hinge sum is the sum over z from n to n + t of Nat.choose (n + t) z * (q - 1) ^ (n + t - z) * (Nat.choose z n - r).
-/

/-- The explicit closed-form upper envelope for the multiple-deletion hinge sum of the constant word. -/
def qary_constant_word_deletion_envelope (t q n r : ℕ) : ℕ := ∑ z ∈ Finset.Icc n (n + t), Nat.choose (n + t) z * (q - 1) ^ (n + t - z) * (Nat.choose z n - r)
