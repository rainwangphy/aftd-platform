import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkExpand

/-!
# longest_common_prefix

Topic: combinatorics   Node: f4a77e1cf769

Provenance: formalization of a published result. Source: arXiv:2611.13676 Lemma 3.1

The longest common prefix of two lists is their maximal shared initial segment.
-/

/-- The longest common prefix of two lists. -/
def longest_common_prefix {α : Type*} [DecidableEq α] : List α → List α → List α
| x :: xs, y :: ys => if x = y then x :: longest_common_prefix xs ys else []
| _, _ => []
