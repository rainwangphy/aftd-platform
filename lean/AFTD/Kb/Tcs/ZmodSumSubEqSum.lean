import AFTD.Prelude

/-!
# zmod_sum_sub_eq_sum

Topic: combinatorics   Node: 494e2f1ce512

Provenance: helper lemma. step towards simple_graph_cycle_power_dyadic_cover_class_model

Summation of any natural function over ZMod n is invariant under subtraction by a constant residue.
-/

/-- Summation of any natural function over ZMod n is invariant under subtraction by a constant residue. -/
theorem zmod_sum_sub_eq_sum
    (n : ℕ) [NeZero n] (g : ZMod n → ℕ) (a : ZMod n) :
    (∑ p : ZMod n, g p) = ∑ v : ZMod n, g (v - a) := by
  exact (Equiv.subRight a).sum_comp g |>.symm
