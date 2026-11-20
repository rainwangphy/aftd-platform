import AFTD.Prelude

/-!
# satisfies_condition_r

Topic: combinatorics   Node: 37985076bc85

Provenance: formalization of a published result. Source: arXiv:2611.22205 Section 3, Condition (R)

For a prime p and natural number r, a function χ : (ZMod p)ˣ → ZMod r, and a map s : α → ZMod p, satisfies_condition_r p r χ s asserts that for every y : ZMod p, there does not exist c : ZMod r such that for all a : α and all proofs h : y + s a ≠ 0, χ (Units.mk0 (y + s a) h) = c.
-/

/-- Condition (R): for every y in ZMod p, the colors chi(y + s_a) for nonzero y + s_a are not all equal. -/
def satisfies_condition_r (p r : ℕ) [Fact p.Prime] (χ : (ZMod p)ˣ → ZMod r) {α : Type*} (s : α → ZMod p) : Prop := ∀ y : ZMod p, ¬ ∃ c : ZMod r, ∀ a : α, ∀ h : y + s a ≠ 0, χ (Units.mk0 (y + s a) h) = c
