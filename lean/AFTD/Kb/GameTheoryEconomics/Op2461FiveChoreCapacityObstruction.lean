import AFTD.Prelude

/-!
# op2461_five_chore_capacity_obstruction

Topic: fair_division   Node: 2eb9881a2f19

Provenance: helper lemma. Finite numeric core of the OP-2461 counterexample; experiments 41658 and 41660.

For the explicitly displayed three-agent five-chore cost table, no allocation keeps the two light agents at cost at most three and the heavy agent at cost at most seven.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem op2461_five_chore_capacity_obstruction :
    let c : Fin 3 → Fin 5 → ℕ := ![![4, 3, 3, 1, 1], ![4, 3, 3, 1, 1], ![6, 2, 2, 1, 1]]
    ∀ σ : Fin 5 → Fin 3,
      ¬ ((∑ e ∈ Finset.univ.filter (fun e => σ e = 0), c 0 e) ≤ 3 ∧
         (∑ e ∈ Finset.univ.filter (fun e => σ e = 1), c 1 e) ≤ 3 ∧
         (∑ e ∈ Finset.univ.filter (fun e => σ e = 2), c 2 e) ≤ 7) := by
  decide
