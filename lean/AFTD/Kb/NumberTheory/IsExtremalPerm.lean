import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes

/-!
# is_extremal_perm

Topic: elementary_number_theory   Node: 41d24abeb46b

Provenance: formalization of a published result. Source: arXiv:2611.04551 Section 2

Given n with [NeZero n], a permutation f of ℤ/nℤ is extremal if the number of its good slopes (the cardinality of good_slopes n f) equals φ(n), where φ is Euler's totient function (Nat.totient n).
-/

/-- A permutation f of ZMod n is extremal if its number of good slopes attains Euler's totient function. -/
def is_extremal_perm (n : ℕ) [NeZero n] (f : Equiv.Perm (ZMod n)) : Prop :=
  (good_slopes n f).card = Nat.totient n
