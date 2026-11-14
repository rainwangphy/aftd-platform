import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# balanced_high_counts_insufficient_for_sharp_mms

Topic: fair_division   Node: 3865788d2484

Provenance: original. Related work: A counterexample to a possible strengthening of the sorted-slot counting argument for OP-1112; experiments 15120 and 26800.

There are seven chores, costs equal to 1 or 3/2, and a bundle S such that three times the number of chores in S is at most 9, three times the number of 3/2-cost chores in S is at most the total number of 3/2-cost chores plus 2, but the cost of S is strictly greater than 5/4 times the three-agent chore maximin share.
-/

theorem balanced_high_counts_insufficient_for_sharp_mms : ∃ (u : Fin 7 → ℝ) (S : Finset (Fin 7)), (∀ g, u g = 1 ∨ u g = 3/2) ∧ 3*S.card ≤ 9 ∧ 3*(S.filter fun g => u g = (3/2:ℝ)).card ≤ (Finset.univ.filter fun g => u g = (3/2:ℝ)).card + 2 ∧ (5/4:ℝ)*chore_maximin_share 3 u < additive_valuation u S := by
  let u : Fin 7 → ℝ := fun (g : Fin 7) => if (g : ℕ) < 4 then (3/2:ℝ) else 1
  let P0 : Fin 7 → Fin 3 := fun (g : Fin 7) => if (g : ℕ) < 2 then (0:Fin 3) else if (g:ℕ) < 4 then 1 else 2
  have hb0 : bundle_of P0 (0:Fin 3) = {0,1} := by ext g; fin_cases g <;> simp [bundle_of, P0]
  have hb1 : bundle_of P0 (1:Fin 3) = {2,3} := by ext g; fin_cases g <;> simp [bundle_of, P0]
  have hb2 : bundle_of P0 (2:Fin 3) = {4,5,6} := by ext g; fin_cases g <;> simp [bundle_of, P0]
  have e0 : additive_valuation u (bundle_of P0 (0:Fin 3)) = 3 := by
    rw [hb0]; simp [u, additive_valuation]
  have e1 : additive_valuation u (bundle_of P0 (1:Fin 3)) = 3 := by
    rw [hb1]; simp [u, additive_valuation]
  have e2 : additive_valuation u (bundle_of P0 (2:Fin 3)) = 3 := by
    rw [hb2]; simp [u, additive_valuation]; norm_num
  have hMMS : chore_maximin_share 3 u ≤ 3 := by
    have h1 : chore_maximin_share 3 u ≤ ⨆ (k : Fin 3), additive_valuation u (bundle_of P0 k) := by
      have h : chore_maximin_share 3 u = ⨅ (P : Fin 7 → Fin 3), ⨆ (k : Fin 3), additive_valuation u (bundle_of P k) := rfl
      rw [h]
      exact ciInf_le (Set.finite_range _).bddBelow P0
    have h2 : (⨆ (k : Fin 3), additive_valuation u (bundle_of P0 k)) ≤ 3 := by
      refine ciSup_le (fun k => ?_)
      fin_cases k
      · exact le_of_eq e0
      · exact le_of_eq e1
      · exact le_of_eq e2
    linarith
  refine ⟨u, {0,1,4}, ?_, ?_, ?_, ?_⟩
  · intro g; simp only [u]; split_ifs <;> norm_num
  · simp
  · have h1 : (({0,1,4} : Finset (Fin 7)).filter (fun g => u g = (3/2:ℝ))) = {0,1} := by
      ext g; fin_cases g <;> simp [u] <;> norm_num
    have h2 : ((Finset.univ : Finset (Fin 7)).filter (fun g => u g = (3/2:ℝ))) = {0,1,2,3} := by
      ext g; fin_cases g <;> simp [u] <;> norm_num
    rw [h1, h2]; simp
  · have hcost : additive_valuation u {0,1,4} = 4 := by
      simp [u, additive_valuation]; norm_num
    rw [hcost]
    linarith
