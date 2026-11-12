import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsOnlineAllocator

/-!
# is_consistent_online_allocator

Topic: fair_division   Node: f65d8f54d4dc

Provenance: original. Related work: arXiv:2505.24321

A horizon-indexed family of two-agent allocation algorithms is a consistent online allocator if each alg m is an online allocator on m chores and the allocation of chore t on a prefix depends only on the costs up to t and is consistent across all horizons.
-/

/-- A family of allocators across horizons m is a consistent online allocator if each alg m is online and decisions on initial prefixes agree across horizons. -/
def is_consistent_online_allocator (alg : (m : ℕ) → (Fin 2 → Fin m → ℝ) → Fin m → Fin 2) : Prop :=
  (∀ m, is_online_allocator 2 m (alg m)) ∧
  ∀ (m₁ m₂ : ℕ) (h : m₁ ≤ m₂) (c : Fin 2 → Fin m₂ → ℝ) (t : Fin m₁),
    alg m₁ (fun i s => c i ⟨s.val, lt_of_lt_of_le s.isLt h⟩) t =
      alg m₂ c ⟨t.val, lt_of_lt_of_le t.isLt h⟩
