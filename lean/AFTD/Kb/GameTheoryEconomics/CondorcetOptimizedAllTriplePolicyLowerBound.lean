import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetStationaryActionDualAcyclicMass
import AFTD.Kb.GameTheoryEconomics.CondorcetMinimalPrivateAveragingObstruction

/-!
# condorcet_optimized_all_triple_policy_lower_bound

Topic: social_choice   Node: 52691cca2c61

Provenance: helper lemma. IN-372 supporting method diagnostic for OP-19. Integer audit experiment9221 and exploratory LP9219. Standard finite LP weak duality; no novelty or research advance is claimed. The original strict election statement remains unchanged.

On the same explicit eight-vertex relation, allow every three-element subset of each root's out-neighborhood, including nonprivate triples. Every nonnegative occupation scheme satisfying triple stationarity has an induced acyclic subset of at least32/101 of its total vertex weight, in homogeneous form. This remains strictly larger than the available unrestricted weight bound5/16 but below one half; it excludes equality of these optimization problems, not strict-half feasibility.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000
def condorcet_policy_gap_all_family (a : Fin 8) : Finset (Finset (Fin 8)) :=
  (univ.powersetCard 3).filter (fun J => ∀ b ∈ J, condorcet_minimal_private_relation a b)
def condorcet_policy_gap_all_sets : Fin 6 → Finset (Fin 8) :=
  ![{3,4},{0,1,2,3,5},{1,2,6},{1,5,6},{2,5,6},{0,7}]
def condorcet_policy_gap_all_coeff : Fin 6 → ℕ := ![23,12,12,12,15,27]
def condorcet_policy_gap_all_potential : Fin 8 → ℕ := ![0,0,0,0,4,0,0,3]
def condorcet_policy_gap_all_orders : Fin 6 → Fin 8 → ℕ :=
  ![![0,0,0,1,0,0,0,0], ![4,3,2,0,0,1,0,0], ![0,1,0,0,0,0,2,0],
    ![0,0,0,0,0,2,1,0], ![0,0,2,0,0,1,0,0], ![0,0,0,0,0,0,0,1]]

theorem condorcet_policy_gap_all_dual_check : ∀ a : Fin 8,
    ∀ J ∈ condorcet_policy_gap_all_family a,
      32 + (∑ b ∈ J, condorcet_policy_gap_all_potential b) ≤
        (∑ j : Fin 6, if a ∈ condorcet_policy_gap_all_sets j then
          condorcet_policy_gap_all_coeff j else 0) +
        3 * condorcet_policy_gap_all_potential a := by decide

theorem condorcet_policy_gap_all_order_check : ∀ j : Fin 6, ∀ a b : Fin 8,
    a ∈ condorcet_policy_gap_all_sets j → b ∈ condorcet_policy_gap_all_sets j →
    condorcet_minimal_private_relation a b →
    condorcet_policy_gap_all_orders j a < condorcet_policy_gap_all_orders j b := by
  decide

theorem condorcet_policy_gap_all_acyclic (j : Fin 6) :
    WellFounded (fun a b : {a : Fin 8 // a ∈ condorcet_policy_gap_all_sets j} =>
      condorcet_minimal_private_relation a.val b.val) := by
  refine (measure (fun a : {a : Fin 8 // a ∈ condorcet_policy_gap_all_sets j} =>
    condorcet_policy_gap_all_orders j a.val)).wf.mono ?_
  intro a b hab
  exact condorcet_policy_gap_all_order_check j a b a.property b.property hab

theorem condorcet_optimized_all_triple_policy_lower_bound
    (x : Fin 8 → Finset (Fin 8) → ℝ) (w : Fin 8 → ℝ)
    (hx : ∀ a, ∀ J ∈ condorcet_policy_gap_all_family a, 0 ≤ x a J)
    (hw : ∀ a, w a = ∑ J ∈ condorcet_policy_gap_all_family a, x a J)
    (hflow : ∀ b, 3 * w b = ∑ a, ∑ J ∈ condorcet_policy_gap_all_family a,
      if b ∈ J then x a J else 0) :
    ∃ A : Finset (Fin 8),
      WellFounded (fun a b : {a : Fin 8 // a ∈ A} =>
        condorcet_minimal_private_relation a.val b.val) ∧
      32 * (∑ a, w a) ≤ 101 * (∑ a ∈ A, w a) := by
  have hdual : ∀ a : Fin 8, ∀ J ∈ condorcet_policy_gap_all_family a,
      (32 : ℝ) + (∑ b ∈ J, (condorcet_policy_gap_all_potential b : ℝ)) ≤
        (∑ j : Fin 6, if a ∈ condorcet_policy_gap_all_sets j then
          (condorcet_policy_gap_all_coeff j : ℝ) else 0) +
        3 * (condorcet_policy_gap_all_potential a : ℝ) := by
    intro a J hJ
    exact_mod_cast condorcet_policy_gap_all_dual_check a J hJ
  obtain ⟨j,hj⟩ := condorcet_stationary_action_dual_acyclic_mass 8 6 (by decide)
    condorcet_policy_gap_all_family x w
    (fun a => (condorcet_policy_gap_all_potential a : ℝ))
    condorcet_policy_gap_all_sets
    (fun j => (condorcet_policy_gap_all_coeff j : ℝ)) 32
    (fun j => Nat.cast_nonneg _) hx hw hflow hdual
  have hsumN : (∑ j : Fin 6, condorcet_policy_gap_all_coeff j) = 101 := by decide
  have hsumR : (∑ j : Fin 6, (condorcet_policy_gap_all_coeff j : ℝ)) = 101 := by
    exact_mod_cast hsumN
  rw [hsumR] at hj
  exact ⟨_, condorcet_policy_gap_all_acyclic j, hj⟩
