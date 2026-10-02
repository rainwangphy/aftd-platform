import AFTD.Prelude

/-!
# any_price_share

Topic: fair_division   Node: 7d65a72d6dd6

The AnyPrice share of an agent with valuation v and entitlement w: the minimum over price vectors p of the most valuable bundle S she can afford, p(S) <= w p(M).
-/

/-- The AnyPrice share (Babaioff-Ezra-Feige; Garg-Sharma Def. 8): `APS = min_p max { v(S) : p(S) ≤ w · p([m]) }` over price vectors `p ∈ ℝ^m`. -/
noncomputable def any_price_share {m : ℕ} (v : Finset (Fin m) → ℝ) (w : ℝ) : ℝ :=
  ⨅ p : Fin m → ℝ, ⨆ S : {S : Finset (Fin m) // ∑ j ∈ S, p j ≤ w * ∑ j, p j}, v S
