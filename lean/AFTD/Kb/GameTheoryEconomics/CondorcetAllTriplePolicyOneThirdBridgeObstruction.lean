import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetStationaryActionDualAcyclicMass

/-!
# condorcet_all_triple_policy_one_third_bridge_obstruction

Topic: social_choice   Node: ceb9e3fd0466

Provenance: helper lemma. IN-372 method diagnostic for OP-19. Targeted computation9290 and exact integer audit9292. No novelty or research advance is claimed. The broad bridge tested here is stronger than the unrefuted strict-half policy condition.

For the explicit six-vertex irreflexive relation with predecessor masks[62,61,35,7,11,19], every set of at most three vertices has an outside common predecessor. No proper induced subset retains this property, and each arrow lies in a three-element out-neighborhood set for which its root is the unique common predecessor. The integer weights[3,3,1,1,1,1] have total10 and put at most3 on any induced acyclic subset. On the other hand, every nonnegative occupation on ALL outgoing three-element sets satisfying triple stationarity has an induced acyclic subset of at least3/8 of its total vertex weight, expressed homogeneously. The rational inequalities3/10<1/3<3/8<1/2 hold. This refutes a proposed policy bound by max(unrestricted optimum,1/3), not the half-threshold policy route or the main election statement.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

def condorcet_six_core_pred : Fin 6 → ℕ := ![62,61,35,7,11,19]
def condorcet_six_core_relation (a b : Fin 6) : Prop :=
  (condorcet_six_core_pred b).testBit a.val = true
instance : DecidableRel condorcet_six_core_relation := fun a b =>
  inferInstanceAs (Decidable ((condorcet_six_core_pred b).testBit a.val = true))
def condorcet_six_core_actions (a : Fin 6) : Finset (Finset (Fin 6)) :=
  (univ.powersetCard 3).filter fun J => ∀ b ∈ J, condorcet_six_core_relation a b
def condorcet_six_core_weight : Fin 6 → ℕ := ![3,3,1,1,1,1]
def condorcet_six_core_sets : Fin 4 → Finset (Fin 6) :=
  ![{3,4,5},{2,4,5},{2,3,5},{2,3,4}]
def condorcet_six_core_orders : Fin 4 → Fin 6 → ℕ :=
  ![![0,0,0,0,1,2],![0,0,2,0,0,1],![0,0,1,2,0,0],![0,0,0,1,2,0]]
def condorcet_six_core_potential : Fin 6 → ℕ := ![3,3,0,0,0,0]
def condorcet_six_core_forbidden : Finset (Finset (Fin 6)) :=
  {{0,1},{0,2},{1,2},{0,3},{1,3},{0,4},{1,4},{0,5},{1,5},{2,3,4,5}}

theorem condorcet_six_core_s3 : ∀ J : Finset (Fin 6), J.card ≤ 3 →
    ∃ a, a ∉ J ∧ ∀ b ∈ J, condorcet_six_core_relation a b := by decide

theorem condorcet_six_core_minimum : ∀ B : Finset (Fin 6),
    (∀ J : Finset (Fin 6), J ⊆ B → J.card ≤ 3 →
      ∃ a, a ∈ B ∧ a ∉ J ∧ ∀ b ∈ J, condorcet_six_core_relation a b) → B = univ := by
  decide

theorem condorcet_six_core_private_arcs : ∀ a b : Fin 6,
    condorcet_six_core_relation a b → ∃ J ∈ condorcet_six_core_actions a,
      b ∈ J ∧ ∀ r, (∀ t ∈ J, condorcet_six_core_relation r t) → r = a := by decide

theorem condorcet_six_core_order_check : ∀ j : Fin 4, ∀ a b : Fin 6,
    a ∈ condorcet_six_core_sets j → b ∈ condorcet_six_core_sets j →
    condorcet_six_core_relation a b →
      condorcet_six_core_orders j a < condorcet_six_core_orders j b := by decide

theorem condorcet_six_core_sets_acyclic (j : Fin 4) :
    WellFounded (fun a b : {a : Fin 6 // a ∈ condorcet_six_core_sets j} =>
      condorcet_six_core_relation a.val b.val) := by
  refine (measure (fun a : {a : Fin 6 // a ∈ condorcet_six_core_sets j} =>
    condorcet_six_core_orders j a.val)).wf.mono ?_
  intro a b hab
  exact condorcet_six_core_order_check j a b a.property b.property hab

theorem condorcet_six_core_dual_check : ∀ a : Fin 6, ∀ J ∈ condorcet_six_core_actions a,
    6 + (∑ b ∈ J, condorcet_six_core_potential b) ≤
      (∑ j : Fin 4, if a ∈ condorcet_six_core_sets j then 4 else 0) +
      3 * condorcet_six_core_potential a := by decide

theorem condorcet_six_core_policy_bound
    (x : Fin 6 → Finset (Fin 6) → ℝ) (w : Fin 6 → ℝ)
    (hx : ∀ a, ∀ J ∈ condorcet_six_core_actions a, 0 ≤ x a J)
    (hw : ∀ a, w a = ∑ J ∈ condorcet_six_core_actions a, x a J)
    (hflow : ∀ b, 3 * w b = ∑ a, ∑ J ∈ condorcet_six_core_actions a,
      if b ∈ J then x a J else 0) :
    ∃ A : Finset (Fin 6),
      WellFounded (fun a b : {a : Fin 6 // a ∈ A} => condorcet_six_core_relation a.val b.val) ∧
      3 * (∑ a, w a) ≤ 8 * (∑ a ∈ A, w a) := by
  have hdual : ∀ a : Fin 6, ∀ J ∈ condorcet_six_core_actions a,
      (6 : ℝ) + (∑ b ∈ J, (condorcet_six_core_potential b : ℝ)) ≤
        (∑ j : Fin 4, if a ∈ condorcet_six_core_sets j then (4 : ℝ) else 0) +
        3 * (condorcet_six_core_potential a : ℝ) := by
    intro a J hJ
    exact_mod_cast condorcet_six_core_dual_check a J hJ
  obtain ⟨j,hj⟩ := condorcet_stationary_action_dual_acyclic_mass 6 4 (by decide)
    condorcet_six_core_actions x w (fun a => (condorcet_six_core_potential a : ℝ))
    condorcet_six_core_sets (fun _ => 4) 6 (by intro j; norm_num) hx hw hflow hdual
  norm_num at hj
  exact ⟨_,condorcet_six_core_sets_acyclic j,by linarith⟩

theorem condorcet_six_core_forbidden_check : ∀ B ∈ condorcet_six_core_forbidden,
    B.Nonempty ∧ ∀ a ∈ B, ∃ b ∈ B, condorcet_six_core_relation b a := by decide

theorem condorcet_six_core_weight_check : ∀ A : Finset (Fin 6),
    (∀ B ∈ condorcet_six_core_forbidden, ¬B ⊆ A) →
      (∑ a ∈ A, condorcet_six_core_weight a) ≤ 3 := by decide

theorem condorcet_six_core_unrestricted_bound (A : Finset (Fin 6))
    (hA : WellFounded (fun a b : {a : Fin 6 // a ∈ A} =>
      condorcet_six_core_relation a.val b.val)) :
    (∑ a ∈ A, condorcet_six_core_weight a) ≤ 3 := by
  apply condorcet_six_core_weight_check A
  intro B hB hsub
  obtain ⟨hne,hpred⟩ := condorcet_six_core_forbidden_check B hB
  obtain ⟨b,hb⟩ := hne
  obtain ⟨a,ha,hmin⟩ := hA.has_min {a : {a : Fin 6 // a ∈ A} | a.val ∈ B}
    ⟨⟨b,hsub hb⟩,hb⟩
  obtain ⟨c,hc,hca⟩ := hpred a.val ha
  exact hmin ⟨c,hsub hc⟩ hc hca

def condorcet_six_core_occupation (a : Fin 6) (J : Finset (Fin 6)) : ℕ :=
  if a = 0 then (if 1 ∈ J then 1 else 0)
  else if a = 1 then (if 0 ∈ J then 1 else 0) else 3
def condorcet_six_core_stationary_weight (a : Fin 6) : ℕ :=
  ∑ J ∈ condorcet_six_core_actions a, condorcet_six_core_occupation a J

theorem condorcet_six_core_stationary_check :
    (∀ a, 0 < condorcet_six_core_stationary_weight a) ∧
    (∑ a : Fin 6, condorcet_six_core_stationary_weight a) = 24 ∧
    (∀ b : Fin 6, 3 * condorcet_six_core_stationary_weight b =
      ∑ a, ∑ J ∈ condorcet_six_core_actions a,
        if b ∈ J then condorcet_six_core_occupation a J else 0) ∧
    (∀ A : Finset (Fin 6),
      (∀ B ∈ condorcet_six_core_forbidden, ¬B ⊆ A) →
      (∑ a ∈ A, condorcet_six_core_stationary_weight a) ≤ 9) := by decide

theorem condorcet_all_triple_policy_one_third_bridge_obstruction :
    (∀ J : Finset (Fin 6), J.card ≤ 3 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, condorcet_six_core_relation a b) ∧
    (∀ B : Finset (Fin 6),
      (∀ J : Finset (Fin 6), J ⊆ B → J.card ≤ 3 →
        ∃ a, a ∈ B ∧ a ∉ J ∧ ∀ b ∈ J, condorcet_six_core_relation a b) → B = univ) ∧
    (∀ a b : Fin 6, condorcet_six_core_relation a b →
      ∃ J ∈ condorcet_six_core_actions a, b ∈ J ∧
        ∀ r, (∀ t ∈ J, condorcet_six_core_relation r t) → r = a) ∧
    (∑ a : Fin 6, condorcet_six_core_weight a) = 10 ∧
    (∀ A : Finset (Fin 6),
      WellFounded (fun a b : {a : Fin 6 // a ∈ A} => condorcet_six_core_relation a.val b.val) →
      (∑ a ∈ A, condorcet_six_core_weight a) ≤ 3) ∧
    (∀ (x : Fin 6 → Finset (Fin 6) → ℝ) (w : Fin 6 → ℝ),
      (∀ a, ∀ J ∈ condorcet_six_core_actions a, 0 ≤ x a J) →
      (∀ a, w a = ∑ J ∈ condorcet_six_core_actions a, x a J) →
      (∀ b, 3 * w b = ∑ a, ∑ J ∈ condorcet_six_core_actions a,
        if b ∈ J then x a J else 0) →
      ∃ A : Finset (Fin 6),
        WellFounded (fun a b : {a : Fin 6 // a ∈ A} => condorcet_six_core_relation a.val b.val) ∧
        3 * (∑ a, w a) ≤ 8 * (∑ a ∈ A, w a)) ∧
    (3 / 10 : ℚ) < 1 / 3 ∧ (1 / 3 : ℚ) < 3 / 8 ∧ (3 / 8 : ℚ) < 1 / 2 := by
  exact ⟨condorcet_six_core_s3,condorcet_six_core_minimum,condorcet_six_core_private_arcs,
    by decide,condorcet_six_core_unrestricted_bound,condorcet_six_core_policy_bound,
    by norm_num,by norm_num,by norm_num⟩
