import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.WeightedChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.Op2461FourThirdsFamilyWeight
import AFTD.Kb.GameTheoryEconomics.Op2461FourThirdsFamilyCost
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# op2461_five_chore_share_upper

Topic: fair_division   Node: ddcc897ec4bb

Provenance: helper lemma. Direct share bounds for the three-agent counterexample to OP-2461; experiment 41660.

In the three-agent five-chore instance, the two light agents have shares at most three and the heavy agent has share at most six.
-/

private lemma op2461_share_le_partition {m n : ℕ} [NeZero n] (w : Fin n → ℝ)
    (u : Fin m → ℝ) (i : Fin n) (P : Fin m → Fin n) (B : ℝ)
    (hw : 0 ≤ w i) (hp : ∀ j, additive_valuation u (bundle_of P j) / w j ≤ B) :
    weighted_chore_maximin_share w u i ≤ w i * B := by
  unfold weighted_chore_maximin_share
  apply mul_le_mul_of_nonneg_left _ hw
  exact ciInf_le_of_le (Set.finite_range _).bddBelow P (ciSup_le hp)

theorem op2461_five_chore_share_upper :
    ∀ i : Fin (3 * 1), weighted_chore_maximin_share (op2461_four_thirds_family_weight 1)
      (op2461_four_thirds_family_cost 1 i) i ≤
        if i.val < 2 then (3 : ℝ) else 6 := by
  let pL : Fin 5 → Fin 3 := ![2, 0, 1, 2, 2]
  let pH : Fin 5 → Fin 3 := ![2, 0, 1, 0, 1]
  have hb : ∀ (i j : Fin 3),
      additive_valuation (op2461_four_thirds_family_cost 1 i)
        (bundle_of (if i.val < 2 then pL else pH) j) /
        op2461_four_thirds_family_weight 1 j ≤ 3 := by
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pL, pH, op2461_four_thirds_family_cost,
        op2461_four_thirds_family_weight, additive_valuation, bundle_of,
        Finset.sum_filter, Fin.sum_univ_succ] <;> simp_all <;> norm_num
  intro i
  have hw : 0 ≤ op2461_four_thirds_family_weight 1 i := by
    fin_cases i <;> norm_num [op2461_four_thirds_family_weight]
  have h := op2461_share_le_partition (op2461_four_thirds_family_weight 1)
    (op2461_four_thirds_family_cost 1 i) i (if i.val < 2 then pL else pH) 3 hw (hb i)
  fin_cases i <;> norm_num [op2461_four_thirds_family_weight] at h ⊢ <;> exact h
