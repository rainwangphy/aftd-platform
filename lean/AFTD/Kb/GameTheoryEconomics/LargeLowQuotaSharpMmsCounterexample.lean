import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare

/-!
# large_low_quota_sharp_mms_counterexample

Topic: fair_division   Node: d594e8259996

Provenance: helper lemma. The counterexample to a proposed OP-1112 large-bundle quota bound in experiment 26950.

With eleven agents and sixty-five chores, there is a bivalued cost function with ratio 7/4 and a bundle of six chores that meets the original one-low quota but costs more than 11/8 times the agent’s eleven-agent chore maximin share.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def in849_low : Finset (Fin 65) := Finset.univ.filter fun g => g.val < 49
private noncomputable def in849_cost (g : Fin 65) : ℝ := if g ∈ in849_low then 1 else 7/4
private def in849_bundle : Finset (Fin 65) := {0, 49, 50, 51, 52, 53}
private def in849_partition (g : Fin 65) : Fin 11 :=
  ⟨if g.val < 49 then g.val / 7 else 7 + (g.val - 49) / 4, by
    have := g.isLt
    split_ifs <;> omega⟩

private lemma in849_value (S : Finset (Fin 65)) :
    additive_valuation in849_cost S =
      ((S ∩ in849_low).card : ℝ) + ((S \ in849_low).card : ℝ) * (7/4) := by
  classical
  simp [additive_valuation, in849_cost, Finset.sum_ite, Finset.sum_const,
    Finset.filter_mem_eq_inter, Finset.filter_notMem_eq_sdiff, nsmul_eq_mul]

private lemma in849_partition_cost (i : Fin 11) :
    additive_valuation in849_cost (bundle_of in849_partition i) = 7 := by
  have hlo : ((bundle_of in849_partition i) ∩ in849_low).card =
      if i.val < 7 then 7 else 0 := by
    fin_cases i <;> decide
  have hhi : ((bundle_of in849_partition i) \ in849_low).card =
      if i.val < 7 then 0 else 4 := by
    fin_cases i <;> decide
  rw [in849_value]
  rw [hlo, hhi]
  fin_cases i <;> norm_num

theorem large_low_quota_sharp_mms_counterexample :
    ∃ (L : Finset (Fin 65)) (u : Fin 65 → ℝ) (S : Finset (Fin 65)),
      (∀ g, u g = if g ∈ L then 1 else (7/4 : ℝ)) ∧
      S.card ≤ 6 ∧ min 6 (L.card / 10) - 6/2 ≤ (S ∩ L).card ∧
      (11/8 : ℝ) * chore_maximin_share 11 u < additive_valuation u S := by
  classical
  have hmms : chore_maximin_share 11 in849_cost ≤ 7 := by
    unfold chore_maximin_share
    exact (ciInf_le (Set.finite_range _).bddBelow in849_partition).trans
      (ciSup_le fun i => (in849_partition_cost i).le)
  refine ⟨in849_low, in849_cost, in849_bundle, ?_, ?_, ?_, ?_⟩
  · intro g; rfl
  · decide
  · decide
  · have hscore : additive_valuation in849_cost in849_bundle = 39/4 := by
      have hlo : (in849_bundle ∩ in849_low).card = 1 := by decide
      have hhi : (in849_bundle \ in849_low).card = 5 := by decide
      rw [in849_value, hlo, hhi]
      norm_num
    rw [hscore]
    linarith
