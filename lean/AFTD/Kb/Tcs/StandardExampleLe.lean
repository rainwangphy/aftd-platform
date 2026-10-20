import AFTD.Prelude
import AFTD.Kb.Tcs.StandardExample

/-!
# standard_example_le

Topic: combinatorics   Node: 446f9df20915

Provenance: formalization of a published result. Source: arXiv:2610.24774 Section 1

In the standard example S_k, min i ≤ max j if and only if i ≠ j, with no relations between two minimal or two maximal elements.
-/

/-- The partial order relation on the standard example: min i ≤ max j iff i ≠ j. -/
def standard_example_le {k : ℕ} : StandardExample k → StandardExample k → Prop
| StandardExample.min i, StandardExample.min j => i = j
| StandardExample.min i, StandardExample.max j => i ≠ j
| StandardExample.max _, StandardExample.min _ => False
| StandardExample.max i, StandardExample.max j => i = j
