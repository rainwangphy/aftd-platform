import AFTD.Prelude

/-!
# proportional_share_alloc

Topic: mechanism_design   Node: 86da91ede9aa

Proportional-share allocation: identity j receives the fraction b_j / W of the work, W being the total bid.
-/

noncomputable def proportional_share_alloc (bids : List ℝ) (j : ℕ) : ℝ :=
  bids.getD j 0 / bids.sum
