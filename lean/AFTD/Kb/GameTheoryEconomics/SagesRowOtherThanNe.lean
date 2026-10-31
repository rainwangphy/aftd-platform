import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SagesRowOtherThan

/-!
# sages_row_other_than_ne

Topic: combinatorial_games   Node: 4d1f38d066ad

Provenance: helper lemma. step towards sages_row_upper_bound_binomial

For S ≥ 2, the canonical other sage of x (seat 1 if x is at seat 0, else seat 0) is not x.
-/

/-- The canonical partner `sages_row_other_than hS x` really is a different sage from `x`. -/
theorem sages_row_other_than_ne {S : ℕ} (hS : 2 ≤ S) (x : Fin S) :
    sages_row_other_than hS x ≠ x := by
  intro h
  have hv := congrArg Fin.val h
  simp only [sages_row_other_than] at hv
  split_ifs at hv with h0 <;> omega
