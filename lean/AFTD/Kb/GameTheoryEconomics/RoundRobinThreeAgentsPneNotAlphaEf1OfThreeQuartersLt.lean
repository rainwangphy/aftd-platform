import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsAlphaEf1
import AFTD.Kb.GameTheoryEconomics.IsPickingSequencePne
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcomeUpdateMem
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.PickingRunsAny
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation
import AFTD.Kb.Tcs.G

/-!
# round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt

Topic: fair_division   Node: 258caebc2435

Provenance: original. Related work: OP-346 (arXiv:2610.23686 Sec. 6): the paper's three-agent bound is α_RR(3) ≤ 15/16 (Proposition 1, 8 goods); its 2/3 bound (Theorem 2) needs at least five agents. Found by an exact LP search over all report profiles (experiments 1520, 1530).

With three agents and eight goods, there is an instance with nonnegative additive valuations and a pure Nash equilibrium of Round-Robin whose outcome is not α-EF1 for any α > 3/4. Witness: agents 1 and 3 value every good 1; agent 2 values goods (0..7) at 2,0,2,2,1,1,1,0; reports: agent 1 the identity, agent 2 ranks 4,5,6 first, agent 3 ranks 0,1,2,4,5,7,3,6. The outcome is A_1 = {0,2,3}, A_2 = {4,5,6}, A_3 = {1,7}: agent 2 gets 3 while A_1 minus any good is worth 4 to it. Hence α_RR(3) ≤ 3/4.
-/

def round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_weight : Fin 3 → Fin 8 → ℕ := fun i g =>
  if i = 1 then ![2, 0, 2, 2, 1, 1, 1, 0] g else 1

def round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_rank : Fin 3 → Fin 8 ≃ Fin 8
  | 0 => Equiv.refl _
  | 1 => ⟨![4, 5, 6, 0, 1, 2, 3, 7], ![3, 4, 5, 6, 0, 1, 2, 7], by decide, by decide⟩
  | 2 => ⟨![0, 1, 2, 4, 5, 7, 3, 6], ![0, 1, 2, 6, 3, 4, 7, 5], by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_outcome :
    picking_sequence_outcome (round_robin_sequence 3 8) round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_rank =
      ![{0, 2, 3}, {4, 5, 6}, {1, 7}] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_runs_le : ∀ i : Fin 3, ∀ S ∈ (picking_runs_any (List.finRange 8) i
    (fun a => List.ofFn (round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_rank a)) (round_robin_sequence 3 8) (fun _ => ∅, ∅)).map
      (fun st => st.1 i),
    ∑ g ∈ S, round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_weight i g ≤
      ∑ g ∈ picking_sequence_outcome (round_robin_sequence 3 8) round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_rank i,
        round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_weight i g := by
  decide +kernel

theorem round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt :
    ∃ (w : Fin 3 → Fin 8 → ℝ) (rank : Fin 3 → Fin 8 ≃ Fin 8),
      (∀ i g, 0 ≤ w i g) ∧
      is_picking_sequence_pne
        (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
        (round_robin_sequence 3 8) rank ∧
      ∀ α : ℝ, 3 / 4 < α → ¬ is_alpha_ef1 α
        (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
        (picking_sequence_outcome (round_robin_sequence 3 8) rank) := by
  refine ⟨fun i g => (round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_weight i g : ℝ),
    round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_rank, ?_, ?_, ?_⟩
  · intro i g
    positivity
  · intro i r
    have hmem := picking_sequence_outcome_update_mem (List.finRange 8) List.mem_finRange
      (round_robin_sequence 3 8) round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_rank i r
    have key := round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_runs_le i _ hmem
    simp only [SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation]
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    exact_mod_cast key
  · intro α hα h
    obtain ⟨g, hg, hle⟩ := h 1 0 (by decide) (by rw [round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_outcome]; decide)
    simp only [SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation] at hle
    rw [← Nat.cast_sum, ← Nat.cast_sum, round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_outcome] at hle
    rw [round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_outcome] at hg
    have h4 : ∀ g ∈ ({0, 2, 3} : Finset (Fin 8)),
        ∑ x ∈ ({0, 2, 3} : Finset (Fin 8)) \ {g}, round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_weight 1 x = 4 := by decide
    have h3 : ∑ x ∈ ({4, 5, 6} : Finset (Fin 8)), round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt_weight 1 x = 3 := by decide
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hle hg
    rw [h4 g hg, h3] at hle
    push_cast at hle
    linarith
