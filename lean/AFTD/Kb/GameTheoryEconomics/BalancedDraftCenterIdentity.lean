import AFTD.Prelude

/-!
# balanced_draft_center_identity

Topic: fair_division   Node: 72e781143886

Provenance: helper lemma. Threshold cancellation for the normalized-utility fluctuation problem OP-1493.

For nonzero denominators, centering the normalized ratio at 2n/(n+1) equals n times ((n-1) times the selected sum minus twice the remaining sum), divided by (n+1) times the total sum.
-/

open scoped BigOperators

theorem balanced_draft_center_identity (n A B : ℝ)
    (hn : n + 1 ≠ 0) (hd : A + B ≠ 0) :
    n*A/(A+B) - 2*n/(n+1) =
      n*((n-1)*A-2*B)/((n+1)*(A+B)) := by
  field_simp
  ring
