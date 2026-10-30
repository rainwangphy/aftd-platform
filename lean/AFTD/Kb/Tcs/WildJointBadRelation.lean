import AFTD.Prelude

/-!
# wild_joint_bad_relation

Topic: graphs   Node: bff559a733ee

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

A symmetric relation R is whole-bad for the block map p if some nonempty proper union of blocks (a nonempty proper set of block indices B, its preimage) has no R-edge crossing it; equivalently the block graph of R is disconnected.
-/

/-- Whole-badness: exists a nonempty proper block cut with no R-edge crossing. -/
def wild_joint_bad_relation (q : ℕ) (p : Fin (3*q) → Fin q) (R : Fin (3*q) → Fin (3*q) → Prop) : Prop := ∃ B : Finset (Fin q), B.Nonempty ∧ B ≠ Finset.univ ∧ ∀ x y, R x y → (p x ∈ B ↔ p y ∈ B)
