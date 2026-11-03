import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71Graph
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71Field
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71Coloring
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71FirstDeviationMinimal
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71ReturnStages
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71ReturnSteps
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71ReturnRank
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71ReturnVertex
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_cycle71_minimal_cycle_steps

Topic: equilibria   Node: 6af1636d22a9

Provenance: helper lemma. The explicit 71-vertex unweighted minimal-deviation cycle for the potential-function question in arXiv:1810.09278, Section 7; experiments 12443, 12444, 12450 and 12452.

Every successive pair of the 33 profiles forms a strong deviation, and no proper subcoalition of its changing vertices has a profitable deviation.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 200000

theorem maxcut_cycle71_minimal_cycle_steps : ∀ i : Fin 33,
    @is_maxcut_strong_deviation _ _ maxcut_cycle71_graph
      (by intro u v; unfold maxcut_cycle71_graph maxcut_cycle71_field SimpleGraph.fromRel; infer_instance) 3
      (maxcut_cycle71_return_stages i)
      (Finset.univ.filter fun v : Fin 71 => maxcut_cycle71_return_stages (i + 1) v ≠ maxcut_cycle71_return_stages i v)
      (maxcut_cycle71_return_stages (i + 1)) ∧
    ∀ S : Finset (Fin 71),
      S ⊂ (Finset.univ.filter fun v : Fin 71 => maxcut_cycle71_return_stages (i + 1) v ≠ maxcut_cycle71_return_stages i v) →
      ¬ ∃ τ : Fin 71 → Fin 3, @is_maxcut_strong_deviation _ _ maxcut_cycle71_graph
        (by intro u v; unfold maxcut_cycle71_graph maxcut_cycle71_field SimpleGraph.fromRel; infer_instance) 3
        (maxcut_cycle71_return_stages i) S τ := by
  intro i
  by_cases hi : i.val = 0
  · have hi0 : i = 0 := Fin.ext (by simpa using hi)
    subst i
    have h0 : maxcut_cycle71_return_stages 0 = maxcut_cycle71_coloring 0 := by
      funext v
      simp [maxcut_cycle71_return_stages]
    have h1 : maxcut_cycle71_return_stages 1 = maxcut_cycle71_coloring 1 := by
      funext v
      simp [maxcut_cycle71_return_stages]
    have hc : (Finset.univ.filter fun v : Fin 71 =>
        maxcut_cycle71_coloring 1 v ≠ maxcut_cycle71_coloring 0 v) =
        (Finset.univ.filter fun v : Fin 71 => v.val < 32) := by
      decide +kernel
    simpa only [zero_add, h0, h1, hc] using maxcut_cycle71_first_deviation_minimal
  · let j : Fin 32 := ⟨i.val - 1, by have := i.isLt; omega⟩
    have hfirst : (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin 33) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    have hnext : (⟨(j.val + 2) % 33, Nat.mod_lt _ (by decide)⟩ : Fin 33) = i + 1 := by
      apply Fin.ext
      change (j.val + 2) % 33 = (i.val + 1) % 33
      congr 1
      dsimp [j]
      omega
    have hs := maxcut_cycle71_return_steps j
    dsimp only at hs
    rw [hfirst, hnext] at hs
    obtain ⟨hd, hc⟩ := hs
    rw [hc]
    refine ⟨hd, ?_⟩
    intro S hS hdev
    have hsempty : S = ∅ := Finset.eq_empty_of_ssubset_singleton hS
    obtain ⟨τ, hτ⟩ := hdev
    rw [hsempty] at hτ
    exact Finset.not_nonempty_empty hτ.1
