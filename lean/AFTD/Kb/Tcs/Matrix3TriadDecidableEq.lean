import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad

/-!
# matrix3_triad_decidable_eq

Topic: algebraic_complexity   Node: 4e53872d4528

Provenance: helper lemma. step towards matrix3_tensor_rank_zmod2_le_22

Two triads over a type with decidable equality are equal exactly when their u, v and w components are equal; hence Matrix3Triad R inherits decidable equality from R. In particular, for R = ZMod 2, `List.Nodup` on lists of triads and any finite enumeration of triads are computable, which is what a reduced-space search needs.
-/

/-- Decidable equality for triads, inherited componentwise; makes `List.Nodup` and finite searches over triads computable. -/
instance matrix3_triad_decidable_eq (R : Type*) [DecidableEq R] : DecidableEq (Matrix3Triad R) := fun a b => decidable_of_iff (a.u = b.u ∧ a.v = b.v ∧ a.w = b.w) (by cases a; cases b; simp [Matrix3Triad.mk.injEq])
