import AFTD.Prelude

/-!
# stake_share_pool

Topic: mechanism_design   Node: d0f6c33fa42e

The stake-share pool L + K max(0, M - W) as a function of the total stake W.
-/

noncomputable def stake_share_pool (L K M W : ℝ) : ℝ :=
  L + K * max 0 (M - W)
