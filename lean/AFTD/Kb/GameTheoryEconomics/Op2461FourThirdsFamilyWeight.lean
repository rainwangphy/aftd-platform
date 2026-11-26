import AFTD.Prelude

/-!
# op2461_four_thirds_family_weight

Topic: fair_division   Node: 459563a422e2

Provenance: helper lemma. Explicit counterexample family for OP-2461; experiments 41658, 41660, 41663.

In the four-thirds family, the first 2r agents have weight one and the last r have weight two.
-/

def op2461_four_thirds_family_weight (r : ℕ) (i : Fin (3 * r)) : ℝ := if i.val < 2 * r then 1 else 2
