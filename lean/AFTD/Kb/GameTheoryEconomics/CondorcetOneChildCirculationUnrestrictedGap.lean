import AFTD.Prelude

/-!
# condorcet_one_child_circulation_unrestricted_gap

Topic: social_choice   Node: 337e422cd2ad

Provenance: helper lemma. IN-372 final method obstruction for OP-19. Exact rational SMT experiment9339 supplied the graph; optimization9340 reconstructed the simple rational certificate; exact integer audit9343 checks the complete certificate. No novelty, election bound or campaign research advance is claimed. Earlier random tests missed this sparse graph. The S3-specific reduction remains unproved.

For the explicit seven-vertex oriented relation with predecessor masks [16,4,65,36,72,3,32], every induced acyclic subset has at most five vertices, so uniform weights have acyclic mass at most 5/7. Every nonnegative stationary occupation on its outgoing singleton actions has an induced acyclic subset of at least 3/4 of total vertex mass, expressed homogeneously. Since 5/7 < 3/4, equality between unrestricted acyclic minimax and the one-child circulation restriction fails in general, even for oriented relations. This graph does not have the S3 predecessor property, which is explicitly certified. It does not refute equality restricted to S3 cores, the strict-half separator goal, or the original election statement.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_one_child_action_dual_bound
    (m : ℕ) (F : Fin m → Finset (Finset (Fin m)))
    (x : Fin m → Finset (Fin m) → ℝ) (w p h : Fin m → ℝ) (c : ℝ)
    (hx : ∀ a, ∀ J ∈ F a, 0 ≤ x a J)
    (hw : ∀ a, w a = ∑ J ∈ F a, x a J)
    (hflow : ∀ b, w b = ∑ a, ∑ J ∈ F a, if b ∈ J then x a J else 0)
    (hdual : ∀ a, ∀ J ∈ F a, c + (∑ b ∈ J, h b) ≤ p a + h a) :
    c * (∑ a, w a) ≤ ∑ a, w a * p a := by
  classical
  have hchildren : (∑ a, ∑ J ∈ F a, x a J * (∑ b ∈ J, h b)) =
      ∑ b, w b * h b := by
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
      ∑ a, ∑ J ∈ F a, x a J * (p a + h a) := by
    apply sum_le_sum
    intro a ha
    apply sum_le_sum
    intro J hJ
    exact mul_le_mul_of_nonneg_left (hdual a J hJ) (hx a J hJ)
  have hleft : (∑ a, ∑ J ∈ F a, x a J * (c + ∑ b ∈ J, h b)) =
      c * (∑ a, w a) + ∑ a, w a * h a := by
    simp_rw [mul_add, sum_add_distrib]
    rw [hchildren]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    rw [← sum_mul, ← hw]
    ring
  have hright : (∑ a, ∑ J ∈ F a, x a J * (p a + h a)) =
      (∑ a, w a * p a) + ∑ a, w a * h a := by
    simp_rw [← sum_mul, ← hw, mul_add]
    rw [sum_add_distrib]
  rw [hleft, hright] at hsum
  linarith

theorem condorcet_one_child_action_dual_acyclic_mass
    (m k : ℕ) (hk : 0 < k)
    (F : Fin m → Finset (Finset (Fin m)))
    (x : Fin m → Finset (Fin m) → ℝ) (w h : Fin m → ℝ)
    (A : Fin k → Finset (Fin m)) (d : Fin k → ℝ) (c : ℝ)
    (hd : ∀ j, 0 ≤ d j)
    (hx : ∀ a, ∀ J ∈ F a, 0 ≤ x a J)
    (hw : ∀ a, w a = ∑ J ∈ F a, x a J)
    (hflow : ∀ b, w b = ∑ a, ∑ J ∈ F a, if b ∈ J then x a J else 0)
    (hdual : ∀ a, ∀ J ∈ F a,
      c + (∑ b ∈ J, h b) ≤ (∑ j, if a ∈ A j then d j else 0) + h a) :
    ∃ j, c * (∑ a, w a) ≤ (∑ i, d i) * (∑ a ∈ A j, w a) := by
  classical
  have hbound := condorcet_one_child_action_dual_bound m F x w
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


def condorcet_one_child_gap_pred : Fin 7 → Finset (Fin 7) :=
  ![{4},{2},{0,6},{2,5},{3,6},{0,1},{5}]
def condorcet_one_child_gap_relation (a b : Fin 7) : Prop := a ∈ condorcet_one_child_gap_pred b
instance (a b : Fin 7) : Decidable (condorcet_one_child_gap_relation a b) := inferInstanceAs (Decidable (a ∈ condorcet_one_child_gap_pred b))
def condorcet_one_child_gap_actions (a : Fin 7) : Finset (Finset (Fin 7)) :=
  (univ.powersetCard 1).filter (fun J => ∀ b ∈ J, condorcet_one_child_gap_relation a b)
def condorcet_one_child_gap_sets : Fin 2 → Finset (Fin 7) := ![{0,1,2,4,5},{0,2,3,5,6}]
def condorcet_one_child_gap_potential : Fin 7 → ℕ := ![0,2,1,2,1,1,2]
def condorcet_one_child_gap_orders : Fin 2 → Fin 7 → ℕ := ![![1,3,2,0,0,4,0],![0,0,3,4,0,1,2]]
def condorcet_one_child_gap_forbidden : Finset (Finset (Fin 7)) := {{0,2,3,4},{0,3,4,5},{1,2,5,6},{0,4,5,6}}

theorem condorcet_one_child_gap_forbidden_check : ∀ B ∈ condorcet_one_child_gap_forbidden,
    B.Nonempty ∧ ∀ a ∈ B, ∃ b ∈ B, condorcet_one_child_gap_relation b a := by decide
theorem condorcet_one_child_gap_card_check : ∀ A : Finset (Fin 7),
    (∀ B ∈ condorcet_one_child_gap_forbidden, ¬B ⊆ A) → A.card ≤ 5 := by decide
theorem condorcet_one_child_gap_card (A : Finset (Fin 7))
    (hA : WellFounded (fun a b : {a : Fin 7 // a ∈ A} => condorcet_one_child_gap_relation a.val b.val)) : A.card ≤ 5 := by
  apply condorcet_one_child_gap_card_check A
  intro B hB hsub
  obtain ⟨hne,hpred⟩ := condorcet_one_child_gap_forbidden_check B hB
  obtain ⟨b,hb⟩ := hne
  obtain ⟨a,ha,hmin⟩ := hA.has_min {a : {a : Fin 7 // a ∈ A} | a.val ∈ B} ⟨⟨b,hsub hb⟩,hb⟩
  obtain ⟨c,hc,hca⟩ := hpred a.val ha
  exact hmin ⟨c,hsub hc⟩ hc hca
theorem condorcet_one_child_gap_order_check : ∀ j : Fin 2, ∀ a b : Fin 7,
    a ∈ condorcet_one_child_gap_sets j → b ∈ condorcet_one_child_gap_sets j →
    condorcet_one_child_gap_relation a b →
    condorcet_one_child_gap_orders j a < condorcet_one_child_gap_orders j b := by decide
theorem condorcet_one_child_gap_acyclic (j : Fin 2) :
    WellFounded (fun a b : {a : Fin 7 // a ∈ condorcet_one_child_gap_sets j} => condorcet_one_child_gap_relation a.val b.val) := by
  refine (measure (fun a : {a : Fin 7 // a ∈ condorcet_one_child_gap_sets j} => condorcet_one_child_gap_orders j a.val)).wf.mono ?_
  intro a b hab
  exact condorcet_one_child_gap_order_check j a b a.property b.property hab
theorem condorcet_one_child_gap_dual_check : ∀ a : Fin 7, ∀ J ∈ condorcet_one_child_gap_actions a,
    3 + (∑ b ∈ J, condorcet_one_child_gap_potential b) ≤
      (∑ j : Fin 2, if a ∈ condorcet_one_child_gap_sets j then 2 else 0) + condorcet_one_child_gap_potential a := by decide
theorem condorcet_one_child_gap_bound
    (x : Fin 7 → Finset (Fin 7) → ℝ) (w : Fin 7 → ℝ)
    (hx : ∀ a, ∀ J ∈ condorcet_one_child_gap_actions a, 0 ≤ x a J)
    (hw : ∀ a, w a = ∑ J ∈ condorcet_one_child_gap_actions a, x a J)
    (hflow : ∀ b, w b = ∑ a, ∑ J ∈ condorcet_one_child_gap_actions a, if b ∈ J then x a J else 0) :
    ∃ A : Finset (Fin 7), WellFounded (fun a b : {a : Fin 7 // a ∈ A} => condorcet_one_child_gap_relation a.val b.val) ∧
      3 * (∑ a, w a) ≤ 4 * (∑ a ∈ A, w a) := by
  have hdual : ∀ a : Fin 7, ∀ J ∈ condorcet_one_child_gap_actions a,
      (3 : ℝ) + (∑ b ∈ J, (condorcet_one_child_gap_potential b : ℝ)) ≤
        (∑ j : Fin 2, if a ∈ condorcet_one_child_gap_sets j then (2 : ℝ) else 0) + (condorcet_one_child_gap_potential a : ℝ) := by
    intro a J hJ
    exact_mod_cast condorcet_one_child_gap_dual_check a J hJ
  obtain ⟨j,hj⟩ := condorcet_one_child_action_dual_acyclic_mass 7 2 (by decide)
    condorcet_one_child_gap_actions x w (fun a => (condorcet_one_child_gap_potential a : ℝ))
    condorcet_one_child_gap_sets (fun _ => 2) 3 (by intro j; norm_num) hx hw hflow hdual
  norm_num at hj
  exact ⟨_,condorcet_one_child_gap_acyclic j,hj⟩

def condorcet_one_child_gap_cycle_weight : Fin 7 → ℕ := ![1,0,1,1,1,0,0]
def condorcet_one_child_gap_cycle_next : Fin 7 → Fin 7 := ![2,0,3,4,0,0,0]
def condorcet_one_child_gap_cycle_x (a : Fin 7) (J : Finset (Fin 7)) : ℕ :=
  if J = {condorcet_one_child_gap_cycle_next a} then condorcet_one_child_gap_cycle_weight a else 0
theorem condorcet_one_child_gap_cycle_check :
    (∑ a : Fin 7, condorcet_one_child_gap_cycle_weight a) = 4 ∧
    (∀ a, condorcet_one_child_gap_cycle_weight a = ∑ J ∈ condorcet_one_child_gap_actions a, condorcet_one_child_gap_cycle_x a J) ∧
    (∀ b, condorcet_one_child_gap_cycle_weight b = ∑ a, ∑ J ∈ condorcet_one_child_gap_actions a,
      if b ∈ J then condorcet_one_child_gap_cycle_x a J else 0) := by decide

theorem condorcet_one_child_circulation_unrestricted_gap :
    (∀ a b : Fin 7, condorcet_one_child_gap_relation a b → ¬condorcet_one_child_gap_relation b a) ∧
    (¬∀ J : Finset (Fin 7), J.card ≤ 3 → ∃ a, a ∉ J ∧ ∀ b ∈ J, condorcet_one_child_gap_relation a b) ∧
    (∀ A : Finset (Fin 7), WellFounded (fun a b : {a : Fin 7 // a ∈ A} => condorcet_one_child_gap_relation a.val b.val) → A.card ≤ 5) ∧
    (∀ (x : Fin 7 → Finset (Fin 7) → ℝ) (w : Fin 7 → ℝ),
      (∀ a, ∀ J ∈ condorcet_one_child_gap_actions a, 0 ≤ x a J) →
      (∀ a, w a = ∑ J ∈ condorcet_one_child_gap_actions a, x a J) →
      (∀ b, w b = ∑ a, ∑ J ∈ condorcet_one_child_gap_actions a, if b ∈ J then x a J else 0) →
      ∃ A : Finset (Fin 7), WellFounded (fun a b : {a : Fin 7 // a ∈ A} => condorcet_one_child_gap_relation a.val b.val) ∧
        3 * (∑ a, w a) ≤ 4 * (∑ a ∈ A, w a)) ∧
    (5 / 7 : ℚ) < 3 / 4 := by
  exact ⟨by decide,by decide,condorcet_one_child_gap_card,condorcet_one_child_gap_bound,by norm_num⟩
