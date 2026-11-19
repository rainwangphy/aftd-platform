import AFTD.Prelude
import AFTD.Kb.Tcs.CompleteColoringC

/-!
# complete_coloring_B

Topic: quantum   Node: 966f751313dc

Provenance: formalization of a published result. Source: arXiv:2611.19002, Quantum Coloring Games on Complete Graphs, Section 3.4

The critical ratio parameter B(n, m) for the complete coloring game: C/n for m = 2, and the maximum of [C - (m-2)t^2] / [n - (m-2)t] over 0 <= t <= floor((n-1)/(m-2)) for m >= 3.
-/

/-- The critical ratio parameter B for the complete coloring game. -/
def complete_coloring_B (n m : ℕ) : ℚ :=
  let C : ℚ := complete_coloring_C n m
  if m ≤ 2 then C / n
  else
    (Finset.range ((n - 1) / (m - 2) + 1)).sup' Finset.nonempty_range_add_one (fun t =>
      (C - (m - 2 : ℚ) * (t : ℚ) ^ 2) / (n - (m - 2 : ℚ) * (t : ℚ)))
