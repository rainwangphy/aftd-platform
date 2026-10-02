import AFTD.Prelude

/-!
# catch_up_sum_invariant

Topic: combinatorial_games   Node: 58ae28cfc108

In any Catch-Up position, picking a piece x from remaining preserves the total sum of remaining pieces and both players' scores.
-/

/-- In any Catch-Up position, picking a piece x from remaining preserves the total sum of remaining pieces and both players' scores. -/
theorem catch_up_sum_invariant (remaining : Finset ℕ) (x : ℕ) (s_me s_opp : ℕ) (hx : x ∈ remaining) :
    (remaining.erase x).sum (fun y => y) + (s_me + x) + s_opp = remaining.sum (fun y => y) + s_me + s_opp := by
  have := Finset.sum_erase_add remaining (fun y => y) hx
  omega
