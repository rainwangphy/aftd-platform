import AFTD.Prelude
import AFTD.Kb.Tcs.ThriftyGreedyStep
import AFTD.Kb.Tcs.TimelyItem
import AFTD.Kb.Tcs.TimelyBin
import AFTD.Kb.Tcs.InstLinearOrderTimelyItem

/-!
# thrifty_greedy_aux

Topic: online_algorithms   Node: d042522c800e

Provenance: formalization of a published result. Source: arXiv:2611.09611, Section 2

A fuel-bounded recursive procedure `thrifty_greedy_aux : ℕ → Finset TimelyItem → Finset TimelyBin` that, on remaining items `R`, returns `∅` when `fuel = 0` or `R` is empty, and otherwise inserts `thrifty_greedy_step R h` into the recursive call with `fuel - 1` on `R` minus the items of the packed bin.
-/

/-- Fuel-bounded recursion for Thrifty-Greedy. -/
noncomputable def thrifty_greedy_aux : ℕ → Finset TimelyItem → Finset TimelyBin
| 0, _ => ∅
| fuel + 1, R =>
  open Classical in
  if h : R.Nonempty then
    let b := thrifty_greedy_step R h
    insert b (thrifty_greedy_aux fuel (R \ b.items))
  else
    ∅
