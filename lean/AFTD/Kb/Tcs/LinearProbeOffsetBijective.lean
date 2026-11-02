import AFTD.Prelude
import AFTD.Kb.Tcs.LinearProbeOffset

/-!
# linear_probe_offset_bijective

Topic: data_structures   Node: c407b9165efb

Provenance: helper lemma. step towards unit_first_fixed_offset_mean_probe_maximum

For any table size n with [NeZero n], linear_probe_offset n is bijective.
-/

/-- The linear probe offset sequence is a bijection from Fin n to ZMod n. -/
theorem linear_probe_offset_bijective (n : ℕ) [NeZero n] :
    Function.Bijective (linear_probe_offset n) := by
  unfold linear_probe_offset
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro a b hab
    ext
    rw [← ZMod.val_cast_of_lt a.isLt, ← ZMod.val_cast_of_lt b.isLt]
    exact congrArg ZMod.val hab
  · simp
