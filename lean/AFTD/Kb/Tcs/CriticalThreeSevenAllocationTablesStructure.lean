import AFTD.Prelude

/-!
# critical_three_seven_allocation_tables_structure

Topic: combinatorics   Node: 131f6b84f9b1

Provenance: helper lemma. Explicit finite allocation certificate for OP-1112, experiment 26817.

Each of the seven displayed three-round allocation tables assigns every chore once to each agent across rounds, gives the diagonal agent three chores and each other agent two, and assigns at most one of the first four chores to the diagonal agent in round zero.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem critical_three_seven_allocation_tables_structure :
    let T : Fin 7 → Fin 3 → Fin 7 → Fin 3 := ![
      ![![0, 2, 1, 1, 2, 0, 0], ![1, 1, 0, 0, 1, 2, 2], ![2, 0, 2, 2, 0, 1, 1]],
      ![![0, 2, 1, 1, 2, 0, 0], ![1, 0, 0, 2, 1, 1, 2], ![2, 1, 2, 0, 0, 2, 1]],
      ![![2, 1, 2, 0, 1, 0, 0], ![1, 0, 1, 2, 0, 1, 2], ![0, 2, 0, 1, 2, 2, 1]],
      ![![1, 0, 2, 1, 0, 0, 2], ![2, 1, 0, 2, 1, 1, 0], ![0, 2, 1, 0, 2, 2, 1]],
      ![![1, 2, 2, 1, 0, 0, 0], ![0, 1, 1, 0, 2, 1, 2], ![2, 0, 0, 2, 1, 2, 1]],
      ![![0, 1, 2, 2, 0, 1, 0], ![1, 0, 1, 0, 1, 2, 2], ![2, 2, 0, 1, 2, 0, 1]],
      ![![0, 2, 2, 1, 1, 0, 0], ![1, 0, 1, 2, 0, 2, 1], ![2, 1, 0, 0, 2, 1, 2]]
    ]
    (∀ (j : Fin 7) (g : Fin 7) (i : Fin 3),
      (Finset.univ.filter fun t : Fin 3 => T j t g = i).card = 1) ∧
    (∀ (j : Fin 7) (t i : Fin 3),
      (Finset.univ.filter fun g : Fin 7 => T j t g = i).card = if i = t then 3 else 2) ∧
    (∀ j : Fin 7, (Finset.univ.filter fun g : Fin 7 => g.val < 4 ∧ T j 0 g = 0).card ≤ 1) := by
  decide
