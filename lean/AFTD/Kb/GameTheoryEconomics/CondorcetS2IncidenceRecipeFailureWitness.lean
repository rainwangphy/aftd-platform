import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetMinimumS2IncidenceRootPolicyObstruction
import AFTD.Kb.GameTheoryEconomics.CondorcetUniformOutgoingStationaryCoreObstruction

/-!
# condorcet_s2_incidence_recipe_failure_witness

Topic: social_choice   Node: f42ec98aef6a

Provenance: helper lemma. IN-383, OP-19 campaign session9, 2026-10-30. Concrete nonvacuity check for the eight-vertex recipe diagnostic, using core {1,4,7}. Supporting method diagnostic only, not a main-conjecture counterexample or a research novelty claim.

The existing eight-vertex S3 relation actually contains a three-vertex S2 core with the fixed-incidence recipe obstruction: its unique common root together with a core vertex form an acyclic pair of weight3 out of total5. The witness explicitly supplies the core and its pair-predecessor property, so the conditional all-core diagnostic has a concrete instance.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000

theorem condorcet_s2_incidence_recipe_failure_witness :
    ∃ D : Finset (Fin 8), D.card=3 ∧
      (∀ a∈D,∀ b∈D,∃ c∈D,
        condorcet_uniform_outgoing_gap_relation c a ∧
        condorcet_uniform_outgoing_gap_relation c b) ∧
      ∃ r a : Fin 8, r ∉ D ∧ a ∈ D ∧
      (∀ x, (∀ b ∈ D, condorcet_uniform_outgoing_gap_relation x b) ↔ x = r) ∧
      WellFounded (fun x y : {x : Fin 8 // x ∈ ({r,a} : Finset (Fin 8))} =>
        condorcet_uniform_outgoing_gap_relation x.val y.val) ∧
      (let w : Fin 8 → ℕ := fun x => (if x∈D then 1 else 0) + (if x=r then 2 else 0)
       (∑ x,w x) = 5 ∧ (∑ x∈({r,a} : Finset (Fin 8)),w x) = 3) := by
  refine ⟨{1,4,7},by decide,by decide,?_⟩
  exact condorcet_minimum_s2_incidence_root_policy_obstruction {1,4,7}
    (by decide) (by decide)
