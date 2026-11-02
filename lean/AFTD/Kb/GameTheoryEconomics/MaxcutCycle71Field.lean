import AFTD.Prelude

/-!
# maxcut_cycle71_field

Topic: equilibria   Node: bed5a7e50497

Provenance: helper lemma. Explicit regular 71-vertex construction for the unweighted minimal-deviation cycle, supported by experiments 12443, 12444, 12450 and 12452.

The number of anchor neighbors of each fixed color assigned to each core block in the regular 71-vertex construction.
-/

def maxcut_cycle71_field (u j : ℕ) : ℕ :=
  if u < 8 then (if j = 1 then 13 else if j = 2 then 7 else 0)
  else if u < 16 then (if j = 0 then 1 else if j = 1 then 2 else 13)
  else if u < 24 then (if j = 0 then 13 else if j = 1 then 1 else 2)
  else (if j = 0 then 0 else if j = 1 then 7 else 13)
