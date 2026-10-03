import AFTD.Prelude

/-!
# ef1cost_fin_two_cases

Topic: fair_division   Node: 7ae8859e16b1

With two agents p != q, every agent is p or q.
-/

lemma ef1cost_fin_two_cases (p q : Fin 2) (hpq : p ≠ q) (i : Fin 2) : i = p ∨ i = q := by
  omega
