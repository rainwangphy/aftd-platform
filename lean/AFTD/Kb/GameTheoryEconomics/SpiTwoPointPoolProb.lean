import AFTD.Prelude

/-!
# spi_two_point_pool_prob

Topic: mechanism_design   Node: a5ec81fb0c07

Provenance: formalization of a published result. Source: Intrinsic Robustness of Prophet Inequality to Strategic Reward Signaling, NeurIPS 2024 (arXiv:2409.18269), Proposition 3.1 (threshold signaling: pooling probability with T = E[X | accepted]); two-point case

The probability with which the low value joins the accepted signal in the optimal scheme: 1 if T <= E[X], q(h-T)/((1-q)(T-l)) if E[X] < T <= h, 0 if T > h.
-/

/-- The probability with which the low value of a two-point reward joins the pooled (accepted) signal in the optimal scheme of Prop. 3.1: `1` if `T ≤ E[X]`, `q (h - T) / ((1 - q) (T - l))` if `E[X] < T ≤ h`, and `0` if `T > h`. -/
noncomputable def spi_two_point_pool_prob (h l q T : ℝ) : ℝ :=
  if T ≤ q * h + (1 - q) * l then 1 else if T ≤ h then q * (h - T) / ((1 - q) * (T - l)) else 0
