import AFTD.Prelude
import AFTD.Kb.Tcs.Op652Rel
import AFTD.Kb.Tcs.Op652ProgressionImage
import AFTD.Kb.Tcs.Op652DivisorList

/-!
# op652_rel_decidable

Topic: graphs   Node: a2a6f95c838f

Provenance: helper lemma. step towards op_652_half_degree_packing_negation

The coprimality relation on the model carriers is decidable (computably, via Int.gcd), so that kernel `decide` can evaluate degrees, matching conditions and cut counts on the 72-vertex model graph.
-/

/-- Computable decidability of `op652_rel` (reduces to `Int.gcd`), enabling kernel `decide` on the model graph; built by case analysis on the two sides. -/
instance op652_rel_decidable : DecidableRel op652_rel := by
  intro u v
  cases u with
  | inl d => cases v with
    | inl d' => exact isFalse (by simp [op652_rel])
    | inr x  => exact decidable_of_iff (IsCoprime (d.1 : ℤ) x.1) (by simp [op652_rel])
  | inr x => cases v with
    | inl d  => exact isFalse (by simp [op652_rel])
    | inr x' => exact isFalse (by simp [op652_rel])
