import AFTD.Prelude

/-!
# condorcet_two_child_strict_half_bridge_obstruction

Topic: social_choice   Node: cfcce63ec35c

Provenance: helper lemma. IN-380, OP-19 campaign session8, 2026-10-30. Numerical search9453, independent exact integer audit9457, and kernel-checked scratch TwoChildObstruction.lean. Supporting method obstruction; no new election bound, novelty or research advance is claimed.

The explicit nine-vertex oriented relation in the definitions does not have S3. Integer weights totaling65 give every induced acyclic subset weight at most32, strictly below half. Nevertheless every nonnegative stationary occupation scheme on all outgoing two-element actions, with incoming mass twice each vertex marginal, has an induced acyclic subset with at least half the total marginal weight. Thus the general strict-half one-child bridge cannot be extended to two distinct children without extra hypotheses. This is not an election counterexample and does not refute an S3-specific policy claim.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

theorem condorcet_two_child_action_dual_bound
    (m : ℕ) (F : Fin m → Finset (Finset (Fin m)))
    (x : Fin m → Finset (Fin m) → ℝ) (w p h : Fin m → ℝ) (c : ℝ)
    (hx : ∀ a, ∀ J ∈ F a, 0 ≤ x a J)
    (hw : ∀ a, w a = ∑ J ∈ F a, x a J)
    (hflow : ∀ b, 2 * w b = ∑ a, ∑ J ∈ F a, if b ∈ J then x a J else 0)
    (hdual : ∀ a, ∀ J ∈ F a, c + (∑ b ∈ J, h b) ≤ p a + 2 * h a) :
    c * (∑ a, w a) ≤ ∑ a, w a * p a := by
  classical
  have hchildren : (∑ a, ∑ J ∈ F a, x a J * (∑ b ∈ J, h b)) =
      ∑ b, 2 * w b * h b := by
    calc
      (∑ a, ∑ J ∈ F a, x a J * (∑ b ∈ J, h b)) =
          ∑ a, ∑ J ∈ F a, ∑ b : Fin m, if b ∈ J then x a J * h b else 0 := by
        simp [mul_sum]
      _ = ∑ b : Fin m, ∑ a, ∑ J ∈ F a, if b ∈ J then x a J * h b else 0 := by
        simp_rw [sum_comm (s := F _)]
        rw [sum_comm]
      _ = ∑ b, (∑ a, ∑ J ∈ F a, if b ∈ J then x a J else 0) * h b := by
        simp [sum_mul, ite_mul]
      _ = _ := by simp_rw [← hflow]
  have hsum : (∑ a, ∑ J ∈ F a, x a J * (c + ∑ b ∈ J, h b)) ≤
      ∑ a, ∑ J ∈ F a, x a J * (p a + 2 * h a) := by
    apply sum_le_sum
    intro a ha
    apply sum_le_sum
    intro J hJ
    exact mul_le_mul_of_nonneg_left (hdual a J hJ) (hx a J hJ)
  have hleft : (∑ a, ∑ J ∈ F a, x a J * (c + ∑ b ∈ J, h b)) =
      c * (∑ a, w a) + ∑ a, 2 * w a * h a := by
    simp_rw [mul_add, sum_add_distrib]
    rw [hchildren]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    rw [← sum_mul, ← hw]
    ring
  have hright : (∑ a, ∑ J ∈ F a, x a J * (p a + 2 * h a)) =
      (∑ a, w a * p a) + ∑ a, 2 * w a * h a := by
    simp_rw [← sum_mul, ← hw, mul_add]
    rw [sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro a ha
    ring
  rw [hleft, hright] at hsum
  linarith

theorem condorcet_two_child_action_dual_acyclic_mass
    (m k : ℕ) (hk : 0 < k)
    (F : Fin m → Finset (Finset (Fin m)))
    (x : Fin m → Finset (Fin m) → ℝ) (w h : Fin m → ℝ)
    (A : Fin k → Finset (Fin m)) (d : Fin k → ℝ) (c : ℝ)
    (hd : ∀ j, 0 ≤ d j)
    (hx : ∀ a, ∀ J ∈ F a, 0 ≤ x a J)
    (hw : ∀ a, w a = ∑ J ∈ F a, x a J)
    (hflow : ∀ b, 2 * w b = ∑ a, ∑ J ∈ F a, if b ∈ J then x a J else 0)
    (hdual : ∀ a, ∀ J ∈ F a,
      c + (∑ b ∈ J, h b) ≤ (∑ j, if a ∈ A j then d j else 0) + 2 * h a) :
    ∃ j, c * (∑ a, w a) ≤ (∑ i, d i) * (∑ a ∈ A j, w a) := by
  classical
  have hbound := condorcet_two_child_action_dual_bound m F x w
    (fun a => ∑ j, if a ∈ A j then d j else 0) h c hx hw hflow hdual
  have hswap : (∑ a, w a * (∑ j, if a ∈ A j then d j else 0)) =
      ∑ j, d j * (∑ a ∈ A j, w a) := by
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    simp [mul_ite, mul_comm]
  rw [hswap] at hbound
  obtain ⟨j, hj, hmax⟩ := exists_max_image univ (fun j : Fin k => ∑ a ∈ A j, w a)
    ⟨⟨0,hk⟩, mem_univ _⟩
  refine ⟨j, hbound.trans ?_⟩
  rw [sum_mul]
  exact sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hmax i hi) (hd i))

def condorcet_two_child_gap_pred : Fin 9 → Finset (Fin 9) := ![{3,4,6,8},{0,4,5,7},{0,1,5,6},{2,7},{2,5,8},{0,3,6,8},{1,3,4},{0,4,6},{1,2,3,6,7}]
def condorcet_two_child_gap_relation (a b : Fin 9) : Prop := a ∈ condorcet_two_child_gap_pred b
instance (a b : Fin 9) : Decidable (condorcet_two_child_gap_relation a b) := inferInstanceAs (Decidable (a ∈ condorcet_two_child_gap_pred b))
def condorcet_two_child_gap_actions (a : Fin 9) : Finset (Finset (Fin 9)) :=
  (univ.powersetCard 2).filter (fun J => ∀ b ∈ J, condorcet_two_child_gap_relation a b)
def condorcet_two_child_gap_sets : Fin 5 → Finset (Fin 9) := ![{0,1,2,5,7},{2,4,5,7},{1,2,6,8},{0,3,5,6,8},{1,2,3,7,8}]
def condorcet_two_child_gap_coeff : Fin 5 → ℕ := ![1,1,1,2,1]
def condorcet_two_child_gap_potential : Fin 9 → ℕ := ![0,0,0,0,1,0,0,0,0]
def condorcet_two_child_gap_orders : Fin 5 → Fin 9 → ℕ := ![![0,3,4,0,0,1,0,2,0],![0,0,1,0,2,0,0,3,0],![0,0,2,0,0,0,1,0,3],![3,0,0,0,0,4,1,0,2],![0,1,2,3,0,0,0,0,4]]
def condorcet_two_child_gap_forbidden : Finset (Finset (Fin 9)) := {{0,2,3},{0,2,4},{1,2,4},{2,3,5},{0,4,5},{0,1,6},{2,3,6},{2,4,6},{1,5,6},{4,5,6},{0,3,7},{3,4,5,7},{1,6,7},{3,6,7},{0,1,8},{0,2,8},{1,4,8},{1,5,8},{2,5,8},{4,6,8},{0,7,8},{4,7,8}}
def condorcet_two_child_gap_weight : Fin 9 → ℕ := ![6,8,7,3,13,6,8,5,9]

theorem condorcet_two_child_gap_forbidden_check : ∀ B ∈ condorcet_two_child_gap_forbidden,
    B.Nonempty ∧ ∀ a ∈ B, ∃ b ∈ B, condorcet_two_child_gap_relation b a := by decide
theorem condorcet_two_child_gap_weight_check : ∀ A : Finset (Fin 9),
    (∀ B ∈ condorcet_two_child_gap_forbidden, ¬B ⊆ A) →
      (∑ a ∈ A, condorcet_two_child_gap_weight a) ≤ 32 := by decide
theorem condorcet_two_child_gap_mass (A : Finset (Fin 9))
    (hA : WellFounded (fun a b : {a : Fin 9 // a ∈ A} => condorcet_two_child_gap_relation a.val b.val)) :
    (∑ a ∈ A, condorcet_two_child_gap_weight a) ≤ 32 := by
  apply condorcet_two_child_gap_weight_check A
  intro B hB hsub
  obtain ⟨hne,hpred⟩ := condorcet_two_child_gap_forbidden_check B hB
  obtain ⟨b,hb⟩ := hne
  obtain ⟨a,ha,hmin⟩ := hA.has_min {a : {a : Fin 9 // a ∈ A} | a.val ∈ B} ⟨⟨b,hsub hb⟩,hb⟩
  obtain ⟨c,hc,hca⟩ := hpred a.val ha
  exact hmin ⟨c,hsub hc⟩ hc hca

theorem condorcet_two_child_gap_order_check : ∀ j : Fin 5, ∀ a b : Fin 9,
    a ∈ condorcet_two_child_gap_sets j → b ∈ condorcet_two_child_gap_sets j →
    condorcet_two_child_gap_relation a b →
    condorcet_two_child_gap_orders j a < condorcet_two_child_gap_orders j b := by decide
theorem condorcet_two_child_gap_acyclic (j : Fin 5) :
    WellFounded (fun a b : {a : Fin 9 // a ∈ condorcet_two_child_gap_sets j} => condorcet_two_child_gap_relation a.val b.val) := by
  refine (measure (fun a : {a : Fin 9 // a ∈ condorcet_two_child_gap_sets j} => condorcet_two_child_gap_orders j a.val)).wf.mono ?_
  intro a b hab
  exact condorcet_two_child_gap_order_check j a b a.property b.property hab

theorem condorcet_two_child_gap_dual_check : ∀ a : Fin 9, ∀ J ∈ condorcet_two_child_gap_actions a,
    3 + (∑ b ∈ J, condorcet_two_child_gap_potential b) ≤
      (∑ j : Fin 5, if a ∈ condorcet_two_child_gap_sets j then condorcet_two_child_gap_coeff j else 0) +
      2 * condorcet_two_child_gap_potential a := by decide

theorem condorcet_two_child_gap_bound
    (x : Fin 9 → Finset (Fin 9) → ℝ) (w : Fin 9 → ℝ)
    (hx : ∀ a, ∀ J ∈ condorcet_two_child_gap_actions a, 0 ≤ x a J)
    (hw : ∀ a, w a = ∑ J ∈ condorcet_two_child_gap_actions a, x a J)
    (hflow : ∀ b, 2 * w b = ∑ a, ∑ J ∈ condorcet_two_child_gap_actions a, if b ∈ J then x a J else 0) :
    ∃ A : Finset (Fin 9), WellFounded (fun a b : {a : Fin 9 // a ∈ A} => condorcet_two_child_gap_relation a.val b.val) ∧
      (∑ a, w a) ≤ 2 * (∑ a ∈ A, w a) := by
  have hdual : ∀ a : Fin 9, ∀ J ∈ condorcet_two_child_gap_actions a,
      (3 : ℝ) + (∑ b ∈ J, (condorcet_two_child_gap_potential b : ℝ)) ≤
        (∑ j : Fin 5, if a ∈ condorcet_two_child_gap_sets j then (condorcet_two_child_gap_coeff j : ℝ) else 0) +
        2 * (condorcet_two_child_gap_potential a : ℝ) := by
    intro a J hJ
    exact_mod_cast condorcet_two_child_gap_dual_check a J hJ
  obtain ⟨j,hj⟩ := condorcet_two_child_action_dual_acyclic_mass 9 5 (by decide)
    condorcet_two_child_gap_actions x w (fun a => (condorcet_two_child_gap_potential a : ℝ))
    condorcet_two_child_gap_sets (fun j => (condorcet_two_child_gap_coeff j : ℝ)) 3
    (fun j => Nat.cast_nonneg _) hx hw hflow hdual
  have hsumN : (∑ j : Fin 5, condorcet_two_child_gap_coeff j) = 6 := by decide
  have hsumR : (∑ j : Fin 5, (condorcet_two_child_gap_coeff j : ℝ)) = 6 := by exact_mod_cast hsumN
  rw [hsumR] at hj
  exact ⟨_,condorcet_two_child_gap_acyclic j,by linarith⟩

theorem condorcet_two_child_strict_half_bridge_obstruction :
    (∀ a b : Fin 9, condorcet_two_child_gap_relation a b → ¬condorcet_two_child_gap_relation b a) ∧
    (¬∀ J : Finset (Fin 9), J.card ≤ 3 → ∃ a, a ∉ J ∧ ∀ b ∈ J, condorcet_two_child_gap_relation a b) ∧
    ((∑ a : Fin 9, condorcet_two_child_gap_weight a) = 65) ∧
    (∀ A : Finset (Fin 9), WellFounded (fun a b : {a : Fin 9 // a ∈ A} => condorcet_two_child_gap_relation a.val b.val) →
      (∑ a ∈ A, condorcet_two_child_gap_weight a) ≤ 32) ∧
    (∀ (x : Fin 9 → Finset (Fin 9) → ℝ) (w : Fin 9 → ℝ),
      (∀ a, ∀ J ∈ condorcet_two_child_gap_actions a, 0 ≤ x a J) →
      (∀ a, w a = ∑ J ∈ condorcet_two_child_gap_actions a, x a J) →
      (∀ b, 2 * w b = ∑ a, ∑ J ∈ condorcet_two_child_gap_actions a, if b ∈ J then x a J else 0) →
      ∃ A : Finset (Fin 9), WellFounded (fun a b : {a : Fin 9 // a ∈ A} => condorcet_two_child_gap_relation a.val b.val) ∧
        (∑ a, w a) ≤ 2 * (∑ a ∈ A, w a)) ∧
    (2 * (32 : ℕ) < 65) := by
  exact ⟨by decide,by decide,by decide,condorcet_two_child_gap_mass,condorcet_two_child_gap_bound,by decide⟩
