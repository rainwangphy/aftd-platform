import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Pmms3cVerify
import AFTD.Kb.GameTheoryEconomics.IsPmmsFairChores
import AFTD.Kb.GameTheoryEconomics.Pmms3cCostNatEq
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.Pmms3cCost
import AFTD.Kb.GameTheoryEconomics.Pmms3cAgentOf
import AFTD.Kb.GameTheoryEconomics.Pmms3cCostNat

/-!
# pmms3c_verify_sound

Topic: fair_division   Node: 48c4de226432

If the certificate check accepts w for allocation σ, then σ is not PMMS for agent w mod 3.
-/

theorem pmms3c_verify_sound (σ : Fin 9 → Fin 3) (w : ℕ) (h : pmms3c_verify σ w = true) : ¬ is_pmms_fair_chores (fun i g => (pmms3c_cost i g : ℝ)) σ (pmms3c_agent_of w) := by
  unfold pmms3c_verify at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨hij, hsub⟩, hlt⟩ := h
  intro hp
  set i := pmms3c_agent_of w
  set j := pmms3c_agent_of (w / 3)
  set m := w / 9
  have hT : (Finset.univ.filter fun g : Fin 9 => m.testBit g = true) ⊆ bundle_of σ i ∪ bundle_of σ j := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    simp only [bundle_of, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [hg] using hsub g
  have key := hp j (Ne.symm hij) _ hT
  have e1 : bundle_of σ i = Finset.univ.filter fun g => (σ g == i) = true := by
    ext g; simp [bundle_of]
  have e2 : (bundle_of σ i ∪ bundle_of σ j) \ (Finset.univ.filter fun g : Fin 9 => m.testBit g = true) =
      Finset.univ.filter fun g => ((σ g == i || σ g == j) && !(m.testBit g)) = true := by
    ext g; simp [bundle_of]
  rw [e2, e1, ← pmms3c_cost_nat_eq, ← pmms3c_cost_nat_eq, ← pmms3c_cost_nat_eq] at key
  have : (max (pmms3c_cost_nat i fun g => m.testBit g)
      (pmms3c_cost_nat i fun g => (σ g == i || σ g == j) && !(m.testBit g)) : ℝ) <
      (pmms3c_cost_nat i fun g => σ g == i : ℝ) := by exact_mod_cast hlt
  linarith
