import AFTD.Prelude

/-!
# f2_add_eq_zero_iff

Topic: combinatorics   Node: bfc66b973da3

Provenance: helper lemma. folklore

In the vector space of functions from Fin d to ZMod 2, the sum of two vectors b and b' equals zero if and only if b equals b'.
-/

/-- Two vectors in (ZMod 2)^d sum to zero if and only if they are equal. -/
theorem f2_add_eq_zero_iff {d : ℕ} (b b' : Fin d → ZMod 2) :
    b + b' = 0 ↔ b = b' := by
  rw [add_eq_zero_iff_eq_neg]
  have h : -b' = b' := funext fun i => ZMod.neg_eq_self_mod_two (b' i)
  rw [h]
