import AFTD.Prelude
import AFTD.Kb.Tcs.InstLinearOrderTimelyItem
import AFTD.Kb.Tcs.TimelyBin
import AFTD.Kb.Tcs.GreedyPackList
import AFTD.Kb.Tcs.TimelyItem
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# thrifty_greedy_step

Topic: online_algorithms   Node: 81de18077eab

Provenance: formalization of a published result. Source: arXiv:2611.09611, Section 2

For a non-empty set of remaining timely items `R` with witness `hR : R.Nonempty`, `thrifty_greedy_step R hR` returns the `TimelyBin` whose trigger item is the minimal element `p = R.min' hR` under the linear order, whose packing time is `p.deadline`, and whose items consist of `p` together with the items from `(R.erase p).filter (fun q => q.arrival ≤ p.deadline)`, sorted by `(· ≤ ·)`, that fit into the remaining capacity `1 - p.size` according to `greedy_pack_list`.
-/

/-- One step of Thrifty-Greedy: open a bin for the earliest-deadline pending item and greedily fill it. -/
noncomputable def thrifty_greedy_step (R : Finset TimelyItem) (hR : R.Nonempty) : TimelyBin :=
  open Classical in
  let p := R.min' hR
  let t := p.deadline
  let pending := (R.erase p).filter (fun q => q.arrival ≤ t)
  let pendingList := pending.sort (· ≤ ·)
  let others := greedy_pack_list (1 - p.size) pendingList
  { items := insert p others, time := t }
