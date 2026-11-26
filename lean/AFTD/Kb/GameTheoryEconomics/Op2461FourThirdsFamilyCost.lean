import AFTD.Prelude

/-!
# op2461_four_thirds_family_cost

Topic: fair_division   Node: a5fe39fe03ff

Provenance: helper lemma. Explicit counterexample family for OP-2461; experiments 41658, 41660, 41663.

There are r large, 2r medium, and 2r small chores. Light-agent costs for these types are 4, 3, 1; heavy-agent costs are 6, 2, 1.
-/

def op2461_four_thirds_family_cost (r : ℕ) (i : Fin (3 * r)) (e : Fin (5 * r)) : ℝ := if i.val < 2 * r then (if e.val < r then 4 else if e.val < 3 * r then 3 else 1) else (if e.val < r then 6 else if e.val < 3 * r then 2 else 1)
