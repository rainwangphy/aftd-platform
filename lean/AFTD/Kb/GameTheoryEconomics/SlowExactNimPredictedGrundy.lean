import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SlowExactNimTruncate

/-!
# slow_exact_nim_predicted_grundy

Topic: combinatorial_games   Node: 188a392d2be7

Provenance: formalization of a published result. Source: arXiv:2611.14546:207

The explicit Sprague-Grundy function value for a position x on k+1 piles in slow exact k-Nim: with truncated piles y = slow_exact_nim_truncate k x, sum S = ∑ y_i, residue s = S % (2k), and odd count o, it returns 0 if s = k - 1, 1 if s = 2k - 1, and for other residues with r = min(s, 2k - 2 - s), 0 if o ≤ r, 1 if o ≥ r + 4 or (o = r + 2 and y 0 is even), 2 if o = r + 2 and both y 0 and y 1 are odd, and 3 if o = r + 2 and y 0 is odd and y 1 is even.
-/

/-- The explicit Sprague-Grundy formula for slow exact k-Nim with k+1 piles from Theorem 1. -/
noncomputable def slow_exact_nim_predicted_grundy (k : ℕ) (x : Fin (k + 1) → ℕ) : ℕ :=
  let y := slow_exact_nim_truncate k x
  let S := ∑ i : Fin (k + 1), y i
  let s := S % (2 * k)
  let o := (Finset.univ.filter (fun i : Fin (k + 1) => Odd (y i))).card
  if s = k - 1 then 0
  else if s = 2 * k - 1 then 1
  else
    let r := min s (2 * k - 2 - s)
    if o ≤ r then 0
    else if r + 4 ≤ o then 1
    else if o = r + 2 ∧ Even (y 0) then 1
    else if o = r + 2 ∧ Odd (y 0) ∧ Odd (y 1) then 2
    else if o = r + 2 ∧ Odd (y 0) ∧ Even (y 1) then 3
    else 0
