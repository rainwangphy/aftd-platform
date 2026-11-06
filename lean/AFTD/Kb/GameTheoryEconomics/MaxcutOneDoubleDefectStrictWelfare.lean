import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutDefectTwoDeviationWelfareNondecreasing
import AFTD.Kb.GameTheoryEconomics.MaxcutDefectTwoEqualWelfareDeviationStructure
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation

/-!
# maxcut_one_double_defect_strict_welfare

Topic: equilibria   Node: 6683827e1b36

Provenance: helper lemma. Equality-case argument from the defect-two strong-deviation welfare identity.

If a profile has maximum monochromatic degree two and at most one vertex of degree two, every strong deviation strictly increases social welfare.
-/

theorem maxcut_one_double_defect_strict_welfare
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (σ τ : V → Fin k) (C : Finset V)
    (hbound : ∀ v : V, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤ 2)
    (hunique : ∀ u v : V, (Finset.univ.filter fun w => G.Adj u w ∧ σ w = σ u).card = 2 → (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card = 2 → u = v)
    (hdev : is_maxcut_strong_deviation G σ C τ) :
    maxcut_welfare G σ < maxcut_welfare G τ := by
  classical
  have hle := maxcut_defect_two_deviation_welfare_nondecreasing G σ τ C (fun v _ => hbound v) hdev
  by_contra hn
  have heq : maxcut_welfare G σ = maxcut_welfare G τ := by omega
  have hs := maxcut_defect_two_equal_welfare_deviation_structure G σ τ C (fun v _ => hbound v) hdev heq
  obtain ⟨v, hv⟩ := hdev.1
  have hv2 := (hs.1 v hv).1
  have hpos : 0 < (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card := by omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  have hadj : G.Adj v w := (Finset.mem_filter.mp hw).2.1
  have hsame : σ v = σ w := (Finset.mem_filter.mp hw).2.2.symm
  have hwC : w ∈ C := hs.2.1 v hv w hadj hsame
  have hw2 := (hs.1 w hwC).1
  exact (G.ne_of_adj hadj) (hunique v w hv2 hw2)
