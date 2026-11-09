import AFTD.Prelude

/-!
# TimelyItem

Topic: online_algorithms   Node: 307355e1a11c

Provenance: formalization of a published result. Source: arXiv:2611.09611, Section 1.1

A structure `TimelyItem` representing an item in online timely bin packing, with fields `id : ℕ` (a unique natural identifier), `arrival : ℝ` (a real arrival time), `deadline : ℝ` (a real deadline), and `size : ℝ` (a real size).
-/

/-- An item in online timely bin packing with an identifier, arrival time, deadline, and size. -/
structure TimelyItem where
  id : ℕ
  arrival : ℝ
  deadline : ℝ
  size : ℝ
