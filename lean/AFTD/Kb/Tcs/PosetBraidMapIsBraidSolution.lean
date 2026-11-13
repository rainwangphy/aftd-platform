import AFTD.Prelude
import AFTD.Kb.Tcs.IsBraidSolution
import AFTD.Kb.Tcs.PosetBraidMap

/-!
# poset_braid_map_is_braid_solution

Topic: combinatorics   Node: 2b93c1cf0dc8

Provenance: formalization of a published result. Source: scout/2611-15540-solutions-of-the-set-theoretic-quantum-yang-baxter-equation.md:492

For any partially ordered set P with decidable order, poset_braid_map satisfies the braid equation.
-/

lemma poset_braid_map_is_braid_solution_helper (p : Prop) [Decidable p] (ε : ZMod 2) :
    (if p then (if p then ε + 1 else ε) + 1 else if p then ε + 1 else ε) = ε := by
  split_ifs <;> (try fin_cases ε) <;> rfl

/-- The poset braid map D_P is a solution of the braid equation. -/
theorem poset_braid_map_is_braid_solution {P : Type*} [PartialOrder P] [DecidableRel ((· ≤ ·) : P → P → Prop)] :
    is_braid_solution (@poset_braid_map P _ _) := by
  dsimp [is_braid_solution]
  funext ⟨u, v, w⟩
  rcases u with x₁ | ⟨y₁, ε₁⟩ <;> rcases v with x₂ | ⟨y₂, ε₂⟩ <;> rcases w with x₃ | ⟨y₃, ε₃⟩
  all_goals
    dsimp [poset_braid_map]
    try simp only [poset_braid_map_is_braid_solution_helper]
