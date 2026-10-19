import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPickingSequencePne
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsEF1
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcomeUpdateMem
import AFTD.Kb.GameTheoryEconomics.PickingRunsAny
import AFTD.Kb.Tcs.G

/-!
# round_robin_pne_not_ef1_three_agents_eight_goods

Topic: fair_division   Node: e463192cc137

Provenance: formalization of a published result. Source: arXiv:2610.23686 (Revisiting the Fairness of Pure Nash Equilibria of Round-Robin), Proposition 1; goods a,b,c,x,y,z,p,q are 0..7 and agents 1,2,3 are 0,1,2.

There is an instance with 3 agents, 8 goods and strictly positive additive valuations, and a pure Nash equilibrium of the Round-Robin mechanism (sequence 1,2,3,1,2,3,1,2) whose outcome is not EF1. Witness: goods a,b,c,x,y,z,p,q; agents 1 and 3 value every good 1, agent 2 values a,b,c at 8, x,y,z at 5 and p,q at 2; reports a>b>c>x>y>z>p>q, x>y>z>a>b>c>p>q and p>x>y>q>z>a>b>c.
-/

def rr_pne_example_weight : Fin 3 → Fin 8 → ℕ := fun i g =>
  if i = 1 then ![8, 8, 8, 5, 5, 5, 2, 2] g else 1

def rr_pne_example_rank : Fin 3 → Fin 8 ≃ Fin 8
  | 0 => Equiv.refl _
  | 1 => ⟨![3, 4, 5, 0, 1, 2, 6, 7], ![3, 4, 5, 0, 1, 2, 6, 7], by decide, by decide⟩
  | 2 => ⟨![6, 3, 4, 7, 5, 0, 1, 2], ![5, 6, 7, 1, 2, 4, 0, 3], by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem rr_pne_example_outcome :
    picking_sequence_outcome (round_robin_sequence 3 8) rr_pne_example_rank =
      ![{0, 1, 2}, {3, 4, 5}, {6, 7}] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rr_pne_example_runs_le : ∀ i : Fin 3, ∀ S ∈ (picking_runs_any (List.finRange 8) i
    (fun a => List.ofFn (rr_pne_example_rank a)) (round_robin_sequence 3 8) (fun _ => ∅, ∅)).map
      (fun st => st.1 i),
    ∑ g ∈ S, rr_pne_example_weight i g ≤
      ∑ g ∈ picking_sequence_outcome (round_robin_sequence 3 8) rr_pne_example_rank i,
        rr_pne_example_weight i g := by
  decide +kernel

theorem round_robin_pne_not_ef1_three_agents_eight_goods :
    ∃ (w : Fin 3 → Fin 8 → ℝ) (rank : Fin 3 → Fin 8 ≃ Fin 8),
      (∀ i g, 0 < w i g) ∧
      is_picking_sequence_pne
        (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
        (round_robin_sequence 3 8) rank ∧
      ¬ SocialChoice.FairDivision.Indivisible.IsEF1
        (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
        (picking_sequence_outcome (round_robin_sequence 3 8) rank) := by
  refine ⟨fun i g => (rr_pne_example_weight i g : ℝ), rr_pne_example_rank, ?_, ?_, ?_⟩
  · intro i g
    have : 0 < rr_pne_example_weight i g := by revert i g; decide
    show (0 : ℝ) < (rr_pne_example_weight i g : ℝ)
    exact_mod_cast this
  · intro i r
    have hmem := picking_sequence_outcome_update_mem (List.finRange 8) List.mem_finRange
      (round_robin_sequence 3 8) rr_pne_example_rank i r
    have key := rr_pne_example_runs_le i _ hmem
    simp only [SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation]
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    exact_mod_cast key
  · intro h
    obtain ⟨g, hg, hle⟩ := h 1 0 (by decide) (by rw [rr_pne_example_outcome]; decide)
    simp only [SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation] at hle
    rw [← Nat.cast_sum, ← Nat.cast_sum, Nat.cast_le, rr_pne_example_outcome] at hle
    rw [rr_pne_example_outcome] at hg
    have : ∀ g ∈ ({0, 1, 2} : Finset (Fin 8)),
        ¬ (∑ x ∈ ({0, 1, 2} : Finset (Fin 8)) \ {g}, rr_pne_example_weight 1 x ≤
          ∑ x ∈ ({3, 4, 5} : Finset (Fin 8)), rr_pne_example_weight 1 x) := by decide
    exact this g hg hle
