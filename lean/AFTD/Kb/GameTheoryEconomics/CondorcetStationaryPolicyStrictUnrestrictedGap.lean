import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetMinimalPrivateObstructionNoHalfCover
import AFTD.Kb.GameTheoryEconomics.CondorcetOptimizedPrivatePolicyLowerBound
import AFTD.Kb.GameTheoryEconomics.CondorcetOptimizedAllTriplePolicyLowerBound
import AFTD.Kb.GameTheoryEconomics.CondorcetMinimalPrivateAveragingObstruction

/-!
# condorcet_stationary_policy_strict_unrestricted_gap

Topic: social_choice   Node: 8b6bbde052a8

Provenance: helper lemma. IN-372 supporting method diagnostic for OP-19. Integer audit experiment9221 and exploratory LP9219. Standard finite LP weak duality; no novelty or research advance is claimed. The original strict election statement remains unchanged.

For the existing integer weights [1,1,1,1,4,1,3,4] of total16 on the explicit eight-vertex relation, every induced acyclic subset has at most5/16 of the total weight. Moreover5/16<32/101<77/227, separating this unrestricted upper bound from the two stationary-policy lower bounds proved by the dependencies. This is a method diagnostic on an already studied core, not an election counterexample or a research advance.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000
def condorcet_policy_gap_forbidden : Finset (Finset (Fin 8)) :=
  {{0,4},{1,4},{2,4},{0,6},{3,6},{4,6},{2,7},{3,7},{4,7},{5,7},{6,7},
    {3,4,5},{0,1,7},{1,2,5,6}}

theorem condorcet_policy_gap_forbidden_check :
    ∀ B ∈ condorcet_policy_gap_forbidden, B.Nonempty ∧
      ∀ a ∈ B, ∃ b ∈ B, condorcet_minimal_private_relation b a := by decide

theorem condorcet_policy_gap_weight_check : ∀ A : Finset (Fin 8),
    (∀ B ∈ condorcet_policy_gap_forbidden, ¬B ⊆ A) →
    (∑ a ∈ A, condorcet_minimal_private_separator_weight a) ≤ 5 := by decide

theorem condorcet_policy_gap_unrestricted_weight_bound (A : Finset (Fin 8))
    (hA : WellFounded (fun a b : {a : Fin 8 // a ∈ A} =>
      condorcet_minimal_private_relation a.val b.val)) :
    (∑ a ∈ A, condorcet_minimal_private_separator_weight a) ≤ 5 := by
  apply condorcet_policy_gap_weight_check A
  intro B hB hsub
  obtain ⟨hBne,hpred⟩ := condorcet_policy_gap_forbidden_check B hB
  obtain ⟨b,hb⟩ := hBne
  obtain ⟨a,ha,hmin⟩ := hA.has_min {a : {a : Fin 8 // a ∈ A} | a.val ∈ B}
    ⟨⟨b,hsub hb⟩,hb⟩
  obtain ⟨c,hc,hca⟩ := hpred a.val ha
  exact hmin ⟨c,hsub hc⟩ hc hca

theorem condorcet_stationary_policy_strict_unrestricted_gap :
    (∀ A : Finset (Fin 8),
      WellFounded (fun a b : {a : Fin 8 // a ∈ A} =>
        condorcet_minimal_private_relation a.val b.val) →
      16 * (∑ a ∈ A, condorcet_minimal_private_separator_weight a) ≤
        5 * (∑ a : Fin 8, condorcet_minimal_private_separator_weight a)) ∧
    (5 / 16 : ℚ) < 32 / 101 ∧ (32 / 101 : ℚ) < 77 / 227 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  intro A hA
  have h := condorcet_policy_gap_unrestricted_weight_bound A hA
  have htotal : (∑ a : Fin 8, condorcet_minimal_private_separator_weight a) = 16 := by
    decide
  rw [htotal]
  omega
