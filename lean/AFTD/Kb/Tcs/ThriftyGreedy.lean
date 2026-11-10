import AFTD.Prelude
import AFTD.Kb.Tcs.ThriftyGreedyAux
import AFTD.Kb.Tcs.TimelyItem
import AFTD.Kb.Tcs.TimelyBin

/-!
# thrifty_greedy

Topic: online_algorithms   Node: 32d09eb71b6a

Provenance: formalization of a published result. Source: arXiv:2611.09611, Section 2

The Thrifty-Greedy packing `thrifty_greedy I` of an instance `I : Finset TimelyItem`, defined as `thrifty_greedy_aux I.card I`.
-/

/-- The Thrifty-Greedy packing of an instance I. -/
noncomputable def thrifty_greedy (I : Finset TimelyItem) : Finset TimelyBin := thrifty_greedy_aux I.card I
