import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoFacilityMaxCost
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCost
import AFTD.Kb.GameTheoryEconomics.IsClosestCandidate
import AFTD.Kb.GameTheoryEconomics.IsTwoFacilityFeasible

/-!
# fixed_dictator_max_cost_le_of_doubleton

Topic: mechanism_design   Node: 9085887d0545

Provenance: formalization of a published result. Source: scout/2610-18006-truthful-two-facility-location-with-candidate-locations-in.md:1349

In the two-facility location problem on a general metric space with candidate set C and a finite nonempty set of agents, if an agent i approves both facilities (p i 0 = true and p i 1 = true), w 0 is a closest candidate in C to x i, and w 1 is a closest candidate in C \ {w 0} to x i, then for every feasible two-facility solution o from C, the max cost of w is at most 3 times the max cost of o.
-/

theorem fixed_dictator_max_cost_le_of_doubleton_aux_triangle {ι X : Type*} [MetricSpace X]
    (x : ι → X) (p : ι → Fin 2 → Bool) (a : ι) (c c' : Fin 2 → X) :
    two_facility_cost x p a c ≤ two_facility_cost x p a c' + dist (c 0) (c' 0) + dist (c 1) (c' 1) := by
  unfold two_facility_cost
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  have h0 : (if p a 0 = true then dist (x a) (c 0) else 0) ≤
      (if p a 0 = true then dist (x a) (c' 0) else 0) + dist (c 0) (c' 0) := by
    split_ifs with h
    · have := dist_triangle (x a) (c' 0) (c 0)
      rw [dist_comm (c' 0) (c 0)] at this
      linarith
    · have : 0 ≤ dist (c 0) (c' 0) := dist_nonneg
      linarith
  have h1 : (if p a 1 = true then dist (x a) (c 1) else 0) ≤
      (if p a 1 = true then dist (x a) (c' 1) else 0) + dist (c 1) (c' 1) := by
    split_ifs with h
    · have := dist_triangle (x a) (c' 1) (c 1)
      rw [dist_comm (c' 1) (c 1)] at this
      linarith
    · have : 0 ≤ dist (c 1) (c' 1) := dist_nonneg
      linarith
  linarith

/-- Case 1 of Theorem 4.14: if some agent approves both facilities, Fixed-Dictator achieves max cost at most 3 times optimal. -/
theorem fixed_dictator_max_cost_le_of_doubleton {ι X : Type*} [Fintype ι] [Nonempty ι] [MetricSpace X] [DecidableEq X]
    (C : Finset X) (x : ι → X) (p : ι → Fin 2 → Bool)
    (w : Fin 2 → X) (i : ι) (hi0 : p i 0 = true) (hi1 : p i 1 = true)
    (hw0 : IsClosestCandidate C (x i) (w 0)) (hw1 : IsClosestCandidate (C.erase (w 0)) (x i) (w 1))
    (o : Fin 2 → X) (ho : IsTwoFacilityFeasible C o) :
    two_facility_max_cost x p w ≤ 3 * two_facility_max_cost x p o := by
  classical
  have hcw : two_facility_cost x p i w = dist (x i) (w 0) + dist (x i) (w 1) := by
    unfold two_facility_cost
    rw [Fin.sum_univ_two, if_pos hi0, if_pos hi1]
  have hco : two_facility_cost x p i o = dist (x i) (o 0) + dist (x i) (o 1) := by
    unfold two_facility_cost
    rw [Fin.sum_univ_two, if_pos hi0, if_pos hi1]
  have hA : two_facility_cost x p i w ≤ two_facility_cost x p i o := by
    have ho0 : o 0 ∈ C := ho.1
    have ho1 : o 1 ∈ C := ho.2.1
    have hone : o 0 ≠ o 1 := ho.2.2
    rw [hcw, hco]
    rcases eq_or_ne (o 0) (w 0) with h | h
    · have hone' : o 1 ≠ w 0 := by intro hh; exact hone (h.trans hh.symm)
      have hlt : dist (x i) (w 1) ≤ dist (x i) (o 1) :=
        hw1.2 (o 1) (Finset.mem_erase.mpr ⟨hone', ho1⟩)
      have h2 : dist (x i) (w 0) ≤ dist (x i) (o 0) := hw0.2 (o 0) ho0
      linarith
    · have hlt : dist (x i) (w 1) ≤ dist (x i) (o 0) :=
        hw1.2 (o 0) (Finset.mem_erase.mpr ⟨h, ho0⟩)
      have h2 : dist (x i) (w 0) ≤ dist (x i) (o 1) := hw0.2 (o 1) ho1
      linarith
  have hD : dist (w 0) (o 0) + dist (w 1) (o 1) ≤ 2 * two_facility_cost x p i o := by
    have htri0 : dist (w 0) (o 0) ≤ dist (x i) (w 0) + dist (x i) (o 0) := by
      have := dist_triangle (w 0) (x i) (o 0)
      rwa [dist_comm (w 0) (x i)] at this
    have htri1 : dist (w 1) (o 1) ≤ dist (x i) (w 1) + dist (x i) (o 1) := by
      have := dist_triangle (w 1) (x i) (o 1)
      rwa [dist_comm (w 1) (x i)] at this
    rw [hcw, hco] at hA
    rw [hco]
    linarith
  have h_le_max : ∀ a, two_facility_cost x p a o ≤ two_facility_max_cost x p o := by
    intro a
    unfold two_facility_max_cost
    exact Finset.le_sup' (fun j => two_facility_cost x p j o) (Finset.mem_univ a)
  have hper : ∀ a, two_facility_cost x p a w ≤ 3 * two_facility_max_cost x p o := by
    intro a
    have htri := fixed_dictator_max_cost_le_of_doubleton_aux_triangle x p a w o
    have h_ao := h_le_max a
    have h_io := h_le_max i
    linarith
  unfold two_facility_max_cost
  exact Finset.sup'_le Finset.univ_nonempty (fun a => two_facility_cost x p a w) (fun a _ => hper a)
