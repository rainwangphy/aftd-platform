import AFTD.Prelude
import AFTD.Kb.Tcs.TimelyItem
import AFTD.Kb.Tcs.InstLinearOrderTimelyItem

/-!
# greedy_pack_list

Topic: online_algorithms   Node: ff45792ad339

Provenance: formalization of a published result. Source: arXiv:2611.09611, Section 2

Given a remaining capacity `remCap : ℝ` and a list of timely items, `greedy_pack_list remCap : List TimelyItem → Finset TimelyItem` recursively scans the list, returning a `Finset TimelyItem` containing each item whose size does not exceed the remaining capacity (inserting it into the finset and subtracting its size from the remaining capacity), and skipping items that do not fit.
-/

/-- Greedily packs a list of items into remaining capacity, returning a finset of packed items. -/
noncomputable def greedy_pack_list (remCap : ℝ) : List TimelyItem → Finset TimelyItem
| [] => ∅
| x :: xs =>
  open Classical in
  if x.size ≤ remCap then
    insert x (greedy_pack_list (remCap - x.size) xs)
  else
    greedy_pack_list remCap xs
