import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiSubintervalFixedPoint
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# tarski_subinterval_slice_shrink

Topic: algorithms   Node: 2fee5cf868ac

Provenance: helper lemma. step towards tarski_query_complexity_five_le_log_sq

Slicing contraction principle: if x is a fixed point of f on all coordinates j ≠ i within [a, b], then comparing f(x)_i with x_i either shows x is a fixed point, or x ≤ f(x) and f has a fixed point in [x, b], or f(x) ≤ x and f has a fixed point in [a, x].
-/

/-- Slicing contraction principle: a slice fixed point with all other coordinates fixed contracts the search sub-box along coordinate i while preserving the subinterval lattice invariant. -/
theorem tarski_subinterval_slice_shrink (n k : ℕ) [NeZero n]
    (f : (Fin k → Fin n) → (Fin k → Fin n)) (hf : Monotone f)
    (a b : Fin k → Fin n) (ha : a ≤ f a) (hb : f b ≤ b)
    (x : Fin k → Fin n) (hax : a ≤ x) (hxb : x ≤ b) (i : Fin k)
    (hslice : ∀ j : Fin k, j ≠ i → f x j = x j) :
    (f x = x) ∨ (x ≤ f x ∧ ∃ z, x ≤ z ∧ z ≤ b ∧ f z = z) ∨ (f x ≤ x ∧ ∃ z, a ≤ z ∧ z ≤ x ∧ f z = z) := by
  rcases le_total (x i) (f x i) with h | h
  · rcases eq_or_lt_of_le h with he | hlt
    · left
      funext j
      by_cases hj : j = i
      · subst hj; exact he.symm
      · exact hslice j hj
    · right; left
      have hxf : x ≤ f x := by
        intro j
        by_cases hj : j = i
        · subst hj; exact hlt.le
        · rw [hslice j hj]
      exact ⟨hxf, tarski_subinterval_fixed_point n k f hf x b hxb hxf hb⟩
  · right; right
    have hfx : f x ≤ x := by
      intro j
      by_cases hj : j = i
      · subst hj; exact h
      · rw [hslice j hj]
    exact ⟨hfx, tarski_subinterval_fixed_point n k f hf a x hax ha hfx⟩
