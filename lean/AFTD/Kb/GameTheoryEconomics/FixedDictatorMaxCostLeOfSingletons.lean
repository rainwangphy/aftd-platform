import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoFacilityMaxCost
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCost
import AFTD.Kb.GameTheoryEconomics.IsClosestCandidate
import AFTD.Kb.GameTheoryEconomics.IsTwoFacilityFeasible
import AFTD.Kb.GameTheoryEconomics.TwoFacilityMaxCostNonneg
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCostLeMaxCost

/-!
# fixed_dictator_max_cost_le_of_singletons

Topic: mechanism_design   Node: da5e27bc584a

Provenance: formalization of a published result. Source: scout/2610-18006-truthful-two-facility-location-with-candidate-locations-in.md:1390

In the two-facility location problem on a metric space with a finite nonempty set of agents, if no agent approves both facilities, agent i approves facility 0, agent j approves facility 1, facility 0 is placed at a closest candidate of i, and facility 1 at a closest available candidate of j, then the max cost of w is at most 5 times the max cost of any feasible solution o.
-/

/-- Case 2 of Theorem 4.14: when no agent approves both facilities and both facilities are approved, Fixed-Dictator achieves max cost at most 5 times optimal. -/
theorem fixed_dictator_max_cost_le_of_singletons {ι X : Type*} [Fintype ι] [Nonempty ι] [MetricSpace X] [DecidableEq X]
    (C : Finset X) (x : ι → X) (p : ι → Fin 2 → Bool)
    (hnd : ∀ a, ¬ (p a 0 = true ∧ p a 1 = true)) (w : Fin 2 → X) (i j : ι)
    (hi : p i 0 = true) (hj : p j 1 = true)
    (hw0 : IsClosestCandidate C (x i) (w 0)) (hw1 : IsClosestCandidate (C.erase (w 0)) (x j) (w 1))
    (o : Fin 2 → X) (ho : IsTwoFacilityFeasible C o) :
    two_facility_max_cost x p w ≤ 5 * two_facility_max_cost x p o := by
  classical
  obtain ⟨ho0, ho1, ho01⟩ := ho
  have hi1 : p i 1 = false := by
    cases h : p i 1
    · rfl
    · exact absurd ⟨hi, h⟩ (hnd i)
  have hj0 : p j 0 = false := by
    cases h : p j 0
    · rfl
    · exact absurd ⟨h, hj⟩ (hnd j)
  have cost_eq : ∀ a (c : Fin 2 → X), two_facility_cost x p a c =
      (if p a 0 then dist (x a) (c 0) else 0) + (if p a 1 then dist (x a) (c 1) else 0) := by
    intro a c; simp [two_facility_cost, Fin.sum_univ_two]
  set M := two_facility_max_cost x p o with hM
  have hM_nonneg : 0 ≤ M := two_facility_max_cost_nonneg x p o
  have h_le_max : ∀ a, two_facility_cost x p a o ≤ M := by
    intro a
    exact two_facility_cost_le_max_cost x p a o
  set ci := dist (x i) (o 0) with hci
  set cj := dist (x j) (o 1) with hcj
  have hci' : two_facility_cost x p i o = ci := by rw [cost_eq]; simp [hi, hi1, hci]
  have hcj' : two_facility_cost x p j o = cj := by rw [cost_eq]; simp [hj, hj0, hcj]
  have hci_le_M : ci ≤ M := by rw [← hci']; exact h_le_max i
  have hcj_le_M : cj ≤ M := by rw [← hcj']; exact h_le_max j
  have hi_w0 : dist (x i) (w 0) ≤ ci := hw0.2 _ ho0
  set E := 2 * (ci + cj) with hE
  have hci0 : 0 ≤ ci := dist_nonneg
  have hcj0 : 0 ≤ cj := dist_nonneg
  -- the two displacement bounds
  have hD0 : dist (o 0) (w 0) ≤ E := by
    have := dist_triangle (o 0) (x i) (w 0)
    rw [dist_comm (o 0) (x i)] at this
    linarith
  have hD1 : dist (o 1) (w 1) ≤ E := by
    by_cases hwo : w 0 = o 1
    · have ho0e : o 0 ∈ C.erase (w 0) := Finset.mem_erase.2 ⟨by rw [hwo]; exact ho01, ho0⟩
      have h1 : dist (x j) (w 1) ≤ dist (x j) (o 0) := hw1.2 _ ho0e
      have h2 := dist_triangle (x j) (o 1) (o 0)
      have h3 : dist (o 1) (o 0) ≤ 2 * ci := by
        rw [← hwo]
        have := dist_triangle (w 0) (x i) (o 0)
        rw [dist_comm (w 0) (x i)] at this
        linarith
      have h4 := dist_triangle (o 1) (x j) (w 1)
      rw [dist_comm (o 1) (x j)] at h4
      linarith
    · have ho1e : o 1 ∈ C.erase (w 0) := Finset.mem_erase.2 ⟨Ne.symm hwo, ho1⟩
      have h1 : dist (x j) (w 1) ≤ cj := hw1.2 _ ho1e
      have h4 := dist_triangle (o 1) (x j) (w 1)
      rw [dist_comm (o 1) (x j)] at h4
      linarith
  have hE_le : E ≤ 4 * M := by
    dsimp [E]
    linarith
  have hper : ∀ a, two_facility_cost x p a w ≤ 5 * M := by
    intro a
    have hao := h_le_max a
    rw [cost_eq] at hao ⊢
    cases h0 : p a 0 <;> cases h1 : p a 1
    · simp; linarith
    · simp only [h0, h1, Bool.false_eq_true, ↓reduceIte, zero_add] at hao ⊢
      have := dist_triangle (x a) (o 1) (w 1)
      linarith
    · simp only [h0, h1, Bool.false_eq_true, ↓reduceIte, add_zero] at hao ⊢
      have := dist_triangle (x a) (o 0) (w 0)
      linarith
    · exact absurd ⟨h0, h1⟩ (hnd a)
  unfold two_facility_max_cost
  exact Finset.sup'_le Finset.univ_nonempty (fun a => two_facility_cost x p a w) (fun a _ => hper a)
