import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation

/-!
# maxcut_five_cycle_repeats

Topic: equilibria   Node: 21b244fbec59

Provenance: helper lemma. Finite-cycle assembly for maxcut_unweighted_strong_deviation_cycle_exists.

Any five colorings that form a directed cycle of strong deviations repeat periodically to yield an infinite strong-deviation sequence returning to its start after five steps.
-/

theorem maxcut_five_cycle_repeats {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (colors : Fin 5 → V → Fin k)
    (hcycle : ∀ i : Fin 5,
      is_maxcut_strong_deviation G (colors i)
        (Finset.univ.filter fun v => colors (i + 1) v ≠ colors i v)
        (colors (i + 1))) :
    ∃ f : ℕ → V → Fin k,
      f 5 = f 0 ∧ ∀ n, is_maxcut_strong_deviation G (f n)
        (Finset.univ.filter fun v => f (n + 1) v ≠ f n v) (f (n + 1)) := by
  let f : ℕ → V → Fin k := fun n => colors ⟨n % 5, Nat.mod_lt _ (by decide)⟩
  refine ⟨f, ?_, ?_⟩
  · rfl
  · intro n
    have hn : (⟨(n + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) =
        (⟨n % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) + 1 := by
      apply Fin.ext
      simp [Fin.val_add, Nat.add_mod]
    simpa [f, hn] using hcycle ⟨n % 5, Nat.mod_lt _ (by decide)⟩
