import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71Graph
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71Field
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71ReturnStages
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71MinimalCycleSteps
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation

/-!
# maxcut_unweighted_minimal_deviation_cycle_exists

Topic: equilibria   Node: 3b9203891312

Provenance: original. Related work: The explicit 71-vertex unweighted minimal-deviation cycle for the potential-function question in arXiv:1810.09278, Section 7; experiments 12443, 12444, 12450 and 12452.

On the specified unweighted 71-vertex graph there is an infinite three-color strong-deviation sequence returning after 33 steps, and every step is inclusion-minimal: no proper subcoalition of its changing players has a profitable deviation from that step’s starting profile.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 200000

theorem maxcut_unweighted_minimal_deviation_cycle_exists :
    ∃ (d : DecidableRel maxcut_cycle71_graph.Adj) (f : ℕ → Fin 71 → Fin 3),
      f 33 = f 0 ∧ ∀ n,
        @is_maxcut_strong_deviation _ _ maxcut_cycle71_graph d 3 (f n)
          (Finset.univ.filter fun v => f (n + 1) v ≠ f n v) (f (n + 1)) ∧
        ∀ S : Finset (Fin 71),
          S ⊂ (Finset.univ.filter fun v => f (n + 1) v ≠ f n v) →
          ¬ ∃ τ : Fin 71 → Fin 3,
            @is_maxcut_strong_deviation _ _ maxcut_cycle71_graph d 3 (f n) S τ := by
  let d : DecidableRel maxcut_cycle71_graph.Adj := by
    intro u v; unfold maxcut_cycle71_graph maxcut_cycle71_field SimpleGraph.fromRel; infer_instance
  let f : ℕ → Fin 71 → Fin 3 := fun n => maxcut_cycle71_return_stages ⟨n % 33, Nat.mod_lt _ (by decide)⟩
  refine ⟨d, f, ?_, ?_⟩
  · rfl
  · intro n
    have hn : (⟨(n + 1) % 33, Nat.mod_lt _ (by decide)⟩ : Fin 33) =
        (⟨n % 33, Nat.mod_lt _ (by decide)⟩ : Fin 33) + 1 := by
      apply Fin.ext
      simp [Fin.val_add, Nat.add_mod]
    simpa [f, hn] using maxcut_cycle71_minimal_cycle_steps ⟨n % 33, Nat.mod_lt _ (by decide)⟩
