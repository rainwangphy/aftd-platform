import AFTD.Prelude

/-!
# bz3_sum_four

Topic: general_equilibrium   Node: 942909a2cc1e

Expanding a sum over the four subsets of a two-element set of players.
-/

/-- Expanding a sum over the four subsets of a two-element set of players. -/
lemma bz3_sum_four (f : Finset (Fin 3) → ℝ) (a b : Fin 3) (hab : a ≠ b) :
    ∑ x ∈ ({∅, {a}, {b}, {a, b}} : Finset (Finset (Fin 3))), f x = f ∅ + f {a} + f {b} + f {a, b} := by
  have h1 : (∅ : Finset (Fin 3)) ∉ ({{a}, {b}, {a, b}} : Finset (Finset (Fin 3))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(Finset.singleton_ne_empty a).symm, (Finset.singleton_ne_empty b).symm,
      (Finset.insert_ne_empty a {b}).symm⟩
  have h2 : ({a} : Finset (Fin 3)) ∉ ({{b}, {a, b}} : Finset (Finset (Fin 3))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h => hab (Finset.singleton_inj.1 h), fun h => hab ?_⟩
    have : b ∈ ({a} : Finset (Fin 3)) := h ▸ (by simp)
    exact (Finset.mem_singleton.1 this).symm
  have h3 : ({b} : Finset (Fin 3)) ∉ ({{a, b}} : Finset (Finset (Fin 3))) := by
    simp only [Finset.mem_singleton]
    intro h
    have : a ∈ ({b} : Finset (Fin 3)) := h ▸ (by simp)
    exact hab (Finset.mem_singleton.1 this)
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3, Finset.sum_singleton]
  ring
