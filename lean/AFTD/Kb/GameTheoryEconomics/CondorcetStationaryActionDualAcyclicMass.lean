import AFTD.Prelude

/-!
# condorcet_stationary_action_dual_acyclic_mass

Topic: social_choice   Node: 265e44843f14

Provenance: helper lemma. IN-372 supporting method diagnostic for OP-19. Integer audit experiment9221 and exploratory LP9219. Standard finite LP weak duality; no novelty or research advance is claimed. The original strict election statement remains unchanged.

For nonnegative occupations of arbitrary finite families of rooted finite-set actions, let each vertex weight equal the sum of occupations at that root and suppose triple-flow stationarity holds: three times a vertex weight equals its total incoming occupation mass. A real vertex potential and a positive finite number of vertex subsets with nonnegative coefficients, satisfying the displayed local dual inequalities, certify that some subset has coefficient-sum times its mass at least c times total vertex mass. The conclusion is homogeneous and requires neither a positive coefficient sum nor normalization. Action sets need not have cardinality three; the factor three is the specified flow coefficient. The subsets need not be acyclic, so applications verify acyclicity separately.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_stationary_action_dual_bound
    (m : ℕ) (F : Fin m → Finset (Finset (Fin m)))
    (x : Fin m → Finset (Fin m) → ℝ) (w p h : Fin m → ℝ) (c : ℝ)
    (hx : ∀ a, ∀ J ∈ F a, 0 ≤ x a J)
    (hw : ∀ a, w a = ∑ J ∈ F a, x a J)
    (hflow : ∀ b, 3 * w b = ∑ a, ∑ J ∈ F a, if b ∈ J then x a J else 0)
    (hdual : ∀ a, ∀ J ∈ F a, c + (∑ b ∈ J, h b) ≤ p a + 3 * h a) :
    c * (∑ a, w a) ≤ ∑ a, w a * p a := by
  classical
  have hchildren : (∑ a, ∑ J ∈ F a, x a J * (∑ b ∈ J, h b)) =
      ∑ b, 3 * w b * h b := by
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
      ∑ a, ∑ J ∈ F a, x a J * (p a + 3 * h a) := by
    apply sum_le_sum
    intro a ha
    apply sum_le_sum
    intro J hJ
    exact mul_le_mul_of_nonneg_left (hdual a J hJ) (hx a J hJ)
  have hleft : (∑ a, ∑ J ∈ F a, x a J * (c + ∑ b ∈ J, h b)) =
      c * (∑ a, w a) + ∑ a, 3 * w a * h a := by
    simp_rw [mul_add, sum_add_distrib]
    rw [hchildren]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    rw [← sum_mul, ← hw]
    ring
  have hright : (∑ a, ∑ J ∈ F a, x a J * (p a + 3 * h a)) =
      (∑ a, w a * p a) + ∑ a, 3 * w a * h a := by
    simp_rw [← sum_mul, ← hw, mul_add]
    rw [sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro a ha
    ring
  rw [hleft, hright] at hsum
  linarith

theorem condorcet_stationary_action_dual_acyclic_mass
    (m k : ℕ) (hk : 0 < k)
    (F : Fin m → Finset (Finset (Fin m)))
    (x : Fin m → Finset (Fin m) → ℝ) (w h : Fin m → ℝ)
    (A : Fin k → Finset (Fin m)) (d : Fin k → ℝ) (c : ℝ)
    (hd : ∀ j, 0 ≤ d j)
    (hx : ∀ a, ∀ J ∈ F a, 0 ≤ x a J)
    (hw : ∀ a, w a = ∑ J ∈ F a, x a J)
    (hflow : ∀ b, 3 * w b = ∑ a, ∑ J ∈ F a, if b ∈ J then x a J else 0)
    (hdual : ∀ a, ∀ J ∈ F a,
      c + (∑ b ∈ J, h b) ≤ (∑ j, if a ∈ A j then d j else 0) + 3 * h a) :
    ∃ j, c * (∑ a, w a) ≤ (∑ i, d i) * (∑ a ∈ A j, w a) := by
  classical
  have hbound := condorcet_stationary_action_dual_bound m F x w
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
