import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes
import AFTD.Kb.Tcs.PrimeShiftMultiplesBijective

/-!
# good_slopes_mem_iff

Topic: elementary_number_theory   Node: 9c1f969f2159

Provenance: helper lemma. step towards good_slopes_gap_mod_105

A slope m is good for the permutation f of ℤ/nℤ exactly when x ↦ f(x) + m·x is a bijection of ℤ/nℤ: m ∈ D_n(f) ↔ Function.Bijective (fun x => f x + m * x).
-/

/-- Membership characterization of the good-slope set, unfolding the definition. -/
theorem good_slopes_mem_iff (n : ℕ) [NeZero n] (f : Equiv.Perm (ZMod n)) (m : ZMod n) : m ∈ good_slopes n f ↔ Function.Bijective (fun x => f x + m * x) := by first | exact prime_shift_multiples_bijective | (apply prime_shift_multiples_bijective <;> assumption) | (apply prime_shift_multiples_bijective <;> simp_all) | simpa using prime_shift_multiples_bijective | (simp only [good_slopes] at *; first | exact prime_shift_multiples_bijective | (apply prime_shift_multiples_bijective <;> assumption) | (apply prime_shift_multiples_bijective <;> simp_all) | simpa using prime_shift_multiples_bijective)
