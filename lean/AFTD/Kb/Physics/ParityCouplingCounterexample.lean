import AFTD.Prelude

/-!
# parity_coupling_counterexample

Topic: quantum_mechanics   Node: b98f15658f73

Provenance: helper lemma. Exact counterexample to an auxiliary OP-827 proof route, experiments 22515 and 22523.

No nonnegative distribution can have the indicated three-even and two-odd event weights while satisfying the local binary support implications.
-/

open scoped BigOperators in
theorem parity_coupling_counterexample
    (p : (Fin 5 → Bool) → ℝ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∀ s, 0 < p s → s 0 = true → s 2 = true → s 1 = true)
    (h3 : ∀ s, 0 < p s → s 2 = true → s 4 = true → s 3 = true)
    (heven : (∑ s : Fin 5 → Bool, if s 0 = true ∧ s 2 = true ∧ s 4 = true then p s else 0) = (9 : ℝ) / 32)
    (hodd : (∑ s : Fin 5 → Bool, if s 1 = true ∧ s 3 = true then p s else 0) = (27 : ℝ) / 128) : False := by
  have hle : (∑ s : Fin 5 → Bool, if s 0 = true ∧ s 2 = true ∧ s 4 = true then p s else 0) ≤
      ∑ s : Fin 5 → Bool, if s 1 = true ∧ s 3 = true then p s else 0 := by
    apply Finset.sum_le_sum
    intro s hs
    by_cases he : s 0 = true ∧ s 2 = true ∧ s 4 = true
    · by_cases ho : s 1 = true ∧ s 3 = true
      · simp [he, ho]
      · have hz : p s = 0 := by
          by_contra hn
          have hpos : 0 < p s := lt_of_le_of_ne (hp s) (Ne.symm hn)
          have : s 1 = true ∧ s 3 = true := ⟨h1 s hpos he.1 he.2.1, h3 s hpos he.2.1 he.2.2⟩
          exact ho this
        simp [he, ho, hz]
    · simp only [he, ↓reduceIte]
      split_ifs <;> simp_all [hp s]
  rw [heven, hodd] at hle
  norm_num at hle
