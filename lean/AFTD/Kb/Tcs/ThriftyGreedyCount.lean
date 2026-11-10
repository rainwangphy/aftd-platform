import AFTD.Prelude
import AFTD.Kb.Tcs.ThriftyGreedy
import AFTD.Kb.Tcs.TimelyItem
import AFTD.Kb.Tcs.TimelyBin

/-!
# thrifty_greedy_count

Topic: online_algorithms   Node: 0c4a42e5d3f4

Provenance: formalization of a published result. Source: arXiv:2611.09611, Section 2

The number of bins `thrifty_greedy_count I` produced by Thrifty-Greedy on instance `I : Finset TimelyItem`, defined as the cardinality `(thrifty_greedy I).card`.
-/

/-- The number of bins produced by Thrifty-Greedy on instance I. -/
noncomputable def thrifty_greedy_count (I : Finset TimelyItem) : ℕ := (thrifty_greedy I).card
