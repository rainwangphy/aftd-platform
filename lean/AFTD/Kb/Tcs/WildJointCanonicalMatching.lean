import AFTD.Prelude

/-!
# wild_joint_canonical_matching

Topic: graphs   Node: 65297fabfc34

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

The fixed matching on Fin (3q) with isolated vertex 0 and pairs {2k-1, 2k} for k >= 1: (1,2),(3,4),(5,6),...
-/

/-- Canonical matching: 0 isolated, pairs {2k-1,2k}. -/
def wild_joint_canonical_matching (q : ℕ) : Fin (3*q) → Fin (3*q) → Prop := fun a b => a ≠ b ∧ 1 ≤ min a.val b.val ∧ min a.val b.val % 2 = 1 ∧ max a.val b.val = min a.val b.val + 1
