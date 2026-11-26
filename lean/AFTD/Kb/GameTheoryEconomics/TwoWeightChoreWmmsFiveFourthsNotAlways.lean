import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Op2461FiveChoreCapacityObstruction
import AFTD.Kb.GameTheoryEconomics.Op2461FiveChoreShareUpper
import AFTD.Kb.GameTheoryEconomics.Op2461FourThirdsFamilyWeight
import AFTD.Kb.GameTheoryEconomics.Op2461FourThirdsFamilyCost
import AFTD.Kb.GameTheoryEconomics.WeightedChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# two_weight_chore_wmms_five_fourths_not_always

Topic: fair_division   Node: bf04171ed057

Provenance: original. Related work: OP-2461, contradicted by the three-agent five-chore instance found in experiment 41658 and independently checked in 41660; related two-agent theorem https://arxiv.org/html/2510.06581, Theorem 6.

The following universal claim is false: for every number n at least two of agents and every finite number m of chores, every assignment of weights one or two and every nonnegative additive agent-chore cost function admit a complete allocation in which each agent pays at most five fourths of its weighted chore maximin share. An agent’s share is its weight times the minimum over complete partitions into n bundles of the maximum, over recipients, of that agent’s cost for the recipient’s bundle divided by the recipient’s weight.
-/

theorem two_weight_chore_wmms_five_fourths_not_always :
    ¬ (∀ (m n : ℕ), 2 ≤ n → ∀ (w : Fin n → ℝ) (c : Fin n → Fin m → ℝ),
      (∀ i, w i = 1 ∨ w i = 2) → (∀ i e, 0 ≤ c i e) →
      ∃ σ : Fin m → Fin n, ∀ i,
        additive_valuation (c i) (bundle_of σ i) ≤
          (5 / 4 : ℝ) * weighted_chore_maximin_share w (c i) i) := by
  intro H
  obtain ⟨σ, hσ⟩ := H 5 3 (by omega)
    (op2461_four_thirds_family_weight 1) (op2461_four_thirds_family_cost 1)
    (by intro i; fin_cases i <;> norm_num [op2461_four_thirds_family_weight])
    (by intro i e; fin_cases i <;> fin_cases e <;> norm_num [op2461_four_thirds_family_cost])
  let c : Fin 3 → Fin 5 → ℕ := ![![4, 3, 3, 1, 1], ![4, 3, 3, 1, 1], ![6, 2, 2, 1, 1]]
  have hcast (i : Fin 3) :
      additive_valuation (op2461_four_thirds_family_cost 1 i) (bundle_of σ i) =
        ((∑ e ∈ Finset.univ.filter (fun e => σ e = i), c i e : ℕ) : ℝ) := by
    simp only [additive_valuation, bundle_of, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro e he
    fin_cases i <;> fin_cases e <;> norm_num [c, op2461_four_thirds_family_cost]
  have u0 := op2461_five_chore_share_upper 0
  have u1 := op2461_five_chore_share_upper 1
  have u2 := op2461_five_chore_share_upper 2
  norm_num at u0 u1 u2
  have h0 := hσ 0
  have h1 := hσ 1
  have h2 := hσ 2
  rw [hcast 0] at h0
  rw [hcast 1] at h1
  rw [hcast 2] at h2
  have k0 : (∑ e ∈ Finset.univ.filter (fun e => σ e = 0), c 0 e) ≤ 3 := by
    have ht : ((∑ e ∈ Finset.univ.filter (fun e => σ e = 0), c 0 e : ℕ) : ℝ) < 4 := by linarith
    have ht' : (∑ e ∈ Finset.univ.filter (fun e => σ e = 0), c 0 e) < 4 := by exact_mod_cast ht
    omega
  have k1 : (∑ e ∈ Finset.univ.filter (fun e => σ e = 1), c 1 e) ≤ 3 := by
    have ht : ((∑ e ∈ Finset.univ.filter (fun e => σ e = 1), c 1 e : ℕ) : ℝ) < 4 := by linarith
    have ht' : (∑ e ∈ Finset.univ.filter (fun e => σ e = 1), c 1 e) < 4 := by exact_mod_cast ht
    omega
  have k2 : (∑ e ∈ Finset.univ.filter (fun e => σ e = 2), c 2 e) ≤ 7 := by
    have ht : ((∑ e ∈ Finset.univ.filter (fun e => σ e = 2), c 2 e : ℕ) : ℝ) < 8 := by linarith
    have ht' : (∑ e ∈ Finset.univ.filter (fun e => σ e = 2), c 2 e) < 8 := by exact_mod_cast ht
    omega
  exact op2461_five_chore_capacity_obstruction σ ⟨k0, k1, k2⟩
