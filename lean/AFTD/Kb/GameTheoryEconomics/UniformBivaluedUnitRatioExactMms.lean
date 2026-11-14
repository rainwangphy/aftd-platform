import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsUniformBivaluedChores
import AFTD.Kb.GameTheoryEconomics.IsEqualMarginalLottery
import AFTD.Kb.GameTheoryEconomics.IsExPostAlphaMmsChores
import AFTD.Kb.GameTheoryEconomics.TwoAgentBivaluedEqualMarginalSharpMms
import AFTD.Kb.GameTheoryEconomics.IsScaledBivaluedChores

/-!
# uniform_bivalued_unit_ratio_exact_mms

Topic: fair_division   Node: 55ca16c46cd0

Provenance: helper lemma. OP-1697

For any number of chores m and any two-agent chore cost profile c satisfying is_uniform_bivalued_chores 1 c, there exists a lottery p in the standard simplex stdSimplex ℝ (Fin m → Fin 2) satisfying is_equal_marginal_lottery p and is_ex_post_alpha_mms_chores 1 c p.
-/

/-- For unit ratio r = 1, every two-agent uniform bivalued chores instance admits an equal-marginal exact-MMS lottery. -/
theorem uniform_bivalued_unit_ratio_exact_mms
    (m : ℕ) (c : Fin 2 → Fin m → ℝ)
    (hc : is_uniform_bivalued_chores 1 c) :
    ∃ p ∈ stdSimplex ℝ (Fin m → Fin 2),
      is_equal_marginal_lottery p ∧
      is_ex_post_alpha_mms_chores 1 c p := by
  have hc' : is_scaled_bivalued_chores 1 c := by
    refine ⟨fun _ => 1, by intro i; norm_num, ?_⟩
    intro i g
    fin_cases i
    · left; exact hc.1 g
    · rcases hc.2 g with h | h
      · left; exact h
      · left; simpa using h
  obtain ⟨p, hp, hEq, hMMS⟩ :=
    two_agent_bivalued_equal_marginal_sharp_mms (r := (1:ℝ))
      (by norm_num : (1:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 2) m c hc'
  refine ⟨p, hp, hEq, ?_⟩
  simpa using hMMS
