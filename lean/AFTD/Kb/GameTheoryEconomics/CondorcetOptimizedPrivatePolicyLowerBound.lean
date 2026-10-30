import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetStationaryActionDualAcyclicMass
import AFTD.Kb.GameTheoryEconomics.CondorcetMinimalPrivateAveragingObstruction

/-!
# condorcet_optimized_private_policy_lower_bound

Topic: social_choice   Node: c9b1720c789e

Provenance: helper lemma. IN-372 supporting method diagnostic for OP-19. Integer audit experiment9221 and exploratory LP9219. Standard finite LP weak duality; no novelty or research advance is claimed. The original strict election statement remains unchanged.

On the explicit eight-vertex globally minimal, arc-minimal S3 relation from condorcet_minimal_private_averaging_obstruction, every choice of nonnegative occupations on the complete private-triple families satisfying triple stationarity has an induced acyclic subset of at least77/227 of its total vertex weight, in the displayed homogeneous form. This lower bound concerns the best possible private stationary policy; it is below one half and does not refute the election conjecture or the strict-half policy conjecture.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

def condorcet_policy_gap_private_sets : Fin 5 → Finset (Fin 8) :=
  ![{3,4},{0,1,2,3,5},{1,2,6},{1,5,6},{2,5,6}]
def condorcet_policy_gap_private_coeff : Fin 5 → ℕ := ![68,39,39,39,42]
def condorcet_policy_gap_private_potential : Fin 8 → ℕ := ![27,0,0,0,13,0,0,30]
def condorcet_policy_gap_private_orders : Fin 5 → Fin 8 → ℕ :=
  ![![0,0,0,1,0,0,0,0], ![4,3,2,0,0,1,0,0], ![0,1,0,0,0,0,2,0],
    ![0,0,0,0,0,2,1,0], ![0,0,2,0,0,1,0,0]]

theorem condorcet_policy_gap_private_dual_check : ∀ a : Fin 8,
    ∀ J ∈ condorcet_minimal_private_family a,
      77 + (∑ b ∈ J, condorcet_policy_gap_private_potential b) ≤
        (∑ j : Fin 5, if a ∈ condorcet_policy_gap_private_sets j then
          condorcet_policy_gap_private_coeff j else 0) +
        3 * condorcet_policy_gap_private_potential a := by decide

theorem condorcet_policy_gap_private_order_check : ∀ j : Fin 5, ∀ a b : Fin 8,
    a ∈ condorcet_policy_gap_private_sets j → b ∈ condorcet_policy_gap_private_sets j →
    condorcet_minimal_private_relation a b →
    condorcet_policy_gap_private_orders j a < condorcet_policy_gap_private_orders j b := by
  decide

theorem condorcet_policy_gap_private_acyclic (j : Fin 5) :
    WellFounded (fun a b : {a : Fin 8 // a ∈ condorcet_policy_gap_private_sets j} =>
      condorcet_minimal_private_relation a.val b.val) := by
  refine (measure (fun a : {a : Fin 8 // a ∈ condorcet_policy_gap_private_sets j} =>
    condorcet_policy_gap_private_orders j a.val)).wf.mono ?_
  intro a b hab
  exact condorcet_policy_gap_private_order_check j a b a.property b.property hab

theorem condorcet_optimized_private_policy_lower_bound
    (x : Fin 8 → Finset (Fin 8) → ℝ) (w : Fin 8 → ℝ)
    (hx : ∀ a, ∀ J ∈ condorcet_minimal_private_family a, 0 ≤ x a J)
    (hw : ∀ a, w a = ∑ J ∈ condorcet_minimal_private_family a, x a J)
    (hflow : ∀ b, 3 * w b = ∑ a, ∑ J ∈ condorcet_minimal_private_family a,
      if b ∈ J then x a J else 0) :
    ∃ A : Finset (Fin 8),
      WellFounded (fun a b : {a : Fin 8 // a ∈ A} =>
        condorcet_minimal_private_relation a.val b.val) ∧
      77 * (∑ a, w a) ≤ 227 * (∑ a ∈ A, w a) := by
  have hdual : ∀ a : Fin 8, ∀ J ∈ condorcet_minimal_private_family a,
      (77 : ℝ) + (∑ b ∈ J, (condorcet_policy_gap_private_potential b : ℝ)) ≤
        (∑ j : Fin 5, if a ∈ condorcet_policy_gap_private_sets j then
          (condorcet_policy_gap_private_coeff j : ℝ) else 0) +
        3 * (condorcet_policy_gap_private_potential a : ℝ) := by
    intro a J hJ
    exact_mod_cast condorcet_policy_gap_private_dual_check a J hJ
  obtain ⟨j,hj⟩ := condorcet_stationary_action_dual_acyclic_mass 8 5 (by decide)
    condorcet_minimal_private_family x w
    (fun a => (condorcet_policy_gap_private_potential a : ℝ))
    condorcet_policy_gap_private_sets
    (fun j => (condorcet_policy_gap_private_coeff j : ℝ)) 77
    (fun j => Nat.cast_nonneg _) hx hw hflow hdual
  have hsumN : (∑ j : Fin 5, condorcet_policy_gap_private_coeff j) = 227 := by decide
  have hsumR : (∑ j : Fin 5, (condorcet_policy_gap_private_coeff j : ℝ)) = 227 := by
    exact_mod_cast hsumN
  rw [hsumR] at hj
  exact ⟨_, condorcet_policy_gap_private_acyclic j, hj⟩
