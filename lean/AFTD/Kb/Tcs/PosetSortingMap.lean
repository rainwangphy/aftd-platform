import AFTD.Prelude

/-!
# poset_sorting_map

Topic: combinatorics   Node: 41a99684400c

Provenance: formalization of a published result. Source: arXiv:2611.15540 Section 2, (2.1)

For a partially ordered set P, the map R_P on P × P swaps (x, y) to (y, x) if y < x and leaves (x, y) fixed otherwise.
-/

open Classical in
/-- The sorting map R_P : P × P → P × P associated to a partially ordered set P. -/
noncomputable def poset_sorting_map (P : Type*) [PartialOrder P] : P × P → P × P := fun ⟨x, y⟩ => if y < x then (y, x) else (x, y)
