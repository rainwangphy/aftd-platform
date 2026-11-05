import AFTD.Prelude

/-!
# good_slopes

Topic: elementary_number_theory   Node: f5d2e74fac6d

Provenance: formalization of a published result. Source: arXiv:2611.04551 Section 2

Given a natural number n with n ≠ 0 (via [NeZero n]) and a permutation f of ℤ/nℤ, good_slopes n f is the finite set (Finset) of elements m ∈ ℤ/nℤ such that x ↦ f(x) + mx is bijective (Function.Bijective).
-/

/-- The finite set of good slopes m in ZMod n for a permutation f. -/
def good_slopes (n : ℕ) [NeZero n] (f : Equiv.Perm (ZMod n)) : Finset (ZMod n) :=
  Finset.univ.filter (fun m => Function.Bijective (fun x => f x + m * x))
