import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoFacilityMaxCost
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCost
import AFTD.Kb.GameTheoryEconomics.IsClosestCandidate
import AFTD.Kb.GameTheoryEconomics.IsTwoFacilityFeasible

/-!
# fixed_dictator_max_cost_le_of_one_approved

Topic: mechanism_design   Node: deb8a375ba2e

Provenance: formalization of a published result. Source: scout/2610-18006-truthful-two-facility-location-with-candidate-locations-in.md:1441

In the two-facility location problem on a general metric space with candidate set C and a finite nonempty set of agents, if no agent approves facility 1 - k (∀ a, p a (1 - k) = false), agent i approves facility k (p i k = true), w k is a closest candidate in C to x i, and w (1 - k) is a closest candidate in C \ {w k} to x i, then for every feasible two-facility solution o from C, the max cost of w is at most 3 times the max cost of o.
-/

/-- Case 3 of Theorem 4.14: when only one facility is approved, Fixed-Dictator achieves max cost at most 3 times optimal. -/
theorem fixed_dictator_max_cost_le_of_one_approved {ι X : Type*} [Fintype ι] [Nonempty ι] [MetricSpace X] [DecidableEq X]
    (C : Finset X) (x : ι → X) (p : ι → Fin 2 → Bool)
    (w : Fin 2 → X) (k : Fin 2) (hk : ∀ a, p a (1 - k) = false) (i : ι) (hi : p i k = true)
    (hwk : IsClosestCandidate C (x i) (w k))
    (hwk' : IsClosestCandidate (C.erase (w k)) (x i) (w (1 - k)))
    (o : Fin 2 → X) (ho : IsTwoFacilityFeasible C o) :
    two_facility_max_cost x p w ≤ 3 * two_facility_max_cost x p o := by
  have _ := hwk'
  classical
  have hcost : ∀ (a : ι) (c : Fin 2 → X),
      two_facility_cost x p a c = if p a k = true then dist (x a) (c k) else 0 := by
    intro a c
    unfold two_facility_cost
    rw [Finset.sum_eq_single k]
    · intro j hj hjk
      have : j = 1 - k := by omega
      rw [this, hk a]
      simp
    · intro h
      exact absurd (Finset.mem_univ k) h
  have ho0 : o 0 ∈ C := ho.1
  have ho1 : o 1 ∈ C := ho.2.1
  have hok : o k ∈ C := by
    rcases (show k = 0 ∨ k = 1 by omega) with h | h
    · rw [h]; exact ho0
    · rw [h]; exact ho1
  have hci_o : two_facility_cost x p i o = dist (x i) (o k) := by
    rw [hcost i o, if_pos hi]
  have hD : dist (w k) (o k) ≤ 2 * dist (x i) (o k) := by
    have htri : dist (w k) (o k) ≤ dist (w k) (x i) + dist (x i) (o k) :=
      dist_triangle (w k) (x i) (o k)
    have h1 : dist (w k) (x i) ≤ dist (x i) (o k) := by
      rw [dist_comm]; exact hwk.2 (o k) hok
    linarith
  have h_le_max : ∀ a, two_facility_cost x p a o ≤ two_facility_max_cost x p o := by
    intro a
    unfold two_facility_max_cost
    exact Finset.le_sup' (fun j => two_facility_cost x p j o) (Finset.mem_univ a)
  have hio : dist (x i) (o k) ≤ two_facility_max_cost x p o := by
    rw [← hci_o]
    exact h_le_max i
  have hper : ∀ a, two_facility_cost x p a w ≤ 3 * two_facility_max_cost x p o := by
    intro a
    rw [hcost a w]
    split_ifs with h
    · have hao := h_le_max a
      rw [hcost a o, if_pos h] at hao
      have htri := dist_triangle (x a) (o k) (w k)
      rw [dist_comm (o k) (w k)] at htri
      linarith
    · have hnonneg : 0 ≤ dist (x i) (o k) := dist_nonneg
      linarith
  unfold two_facility_max_cost
  exact Finset.sup'_le Finset.univ_nonempty (fun a => two_facility_cost x p a w) (fun a _ => hper a)
