import AFTD.Prelude
import AFTD.Kb.Tcs.TimelyItem

/-!
# TimelyBin

Topic: online_algorithms   Node: bd1c17d2abea

Provenance: formalization of a published result. Source: arXiv:2611.09611, Section 1.1

A structure `TimelyBin` representing a bin in timely bin packing, with fields `items : Finset TimelyItem` (the finite set of items packed in the bin) and `time : ℝ` (the real packing time of the bin).
-/

/-- A bin in timely bin packing, specified by its set of items and its packing time. -/
structure TimelyBin where
  items : Finset TimelyItem
  time : ℝ
