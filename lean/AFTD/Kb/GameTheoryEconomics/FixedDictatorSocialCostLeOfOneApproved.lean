import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCost
import AFTD.Kb.GameTheoryEconomics.TwoFacilitySocialCost
import AFTD.Kb.GameTheoryEconomics.IsTwoFacilityFeasible
import AFTD.Kb.GameTheoryEconomics.IsClosestCandidate
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCostNonneg

/-!
# fixed_dictator_social_cost_le_of_one_approved

Topic: mechanism_design   Node: 41b407df309f

Provenance: helper lemma. Case 3 of the proof of Theorem 4.5 of arXiv:2610.18006 (Truthful two-facility location with candidate locations in metric spaces); serves fixed_dictator_social_cost_le

Case 3 of Theorem 4.5: when only F_k is approved and it is placed at a closest candidate of an approving agent i (the other facility at her second-closest), SC(w) ≤ (2n-1) SC(o) for every feasible o.
-/

theorem fixed_dictator_social_cost_le_of_one_approved {ι X : Type*} [Fintype ι] [MetricSpace X] [DecidableEq X]
    (C : Finset X) (x : ι → X) (p : ι → Fin 2 → Bool)
    (w : Fin 2 → X) (k : Fin 2) (hk : ∀ a, p a (1 - k) = false) (i : ι) (hi : p i k = true)
    (hwk : IsClosestCandidate C (x i) (w k))
    (hwk' : IsClosestCandidate (C.erase (w k)) (x i) (w (1 - k)))
    (o : Fin 2 → X) (ho : IsTwoFacilityFeasible C o) :
    two_facility_social_cost x p w ≤ (2 * (Fintype.card ι : ℝ) - 1) * two_facility_social_cost x p o := by
  classical
  have hcost : ∀ (a : ι) (c : Fin 2 → X),
      two_facility_cost x p a c = if p a k = true then dist (x a) (c k) else 0 := by
    intro a c
    unfold two_facility_cost
    rw [Finset.sum_eq_single k]
    · intro j hj _
      have hjk : j = 1 - k := by omega
      rw [hjk, hk a]
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
  have hci_w : two_facility_cost x p i w = dist (x i) (w k) := by
    rw [hcost i w, if_pos hi]
  have hA : two_facility_cost x p i w ≤ two_facility_cost x p i o := by
    rw [hci_w, hci_o]
    exact hwk.2 (o k) hok
  have hD : dist (w k) (o k) ≤ 2 * two_facility_cost x p i o := by
    have htri : dist (w k) (o k) ≤ dist (w k) (x i) + dist (x i) (o k) :=
      dist_triangle (w k) (x i) (o k)
    have h1 : dist (w k) (x i) ≤ dist (x i) (o k) := by
      rw [dist_comm]; exact hwk.2 (o k) hok
    rw [hci_o]
    linarith
  have hper : ∀ a, two_facility_cost x p a w ≤ two_facility_cost x p a o + dist (w k) (o k) := by
    intro a
    rw [hcost a w, hcost a o]
    split_ifs with h
    · have htri := dist_triangle (x a) (o k) (w k)
      rw [dist_comm (o k) (w k)] at htri
      linarith
    · have hnn := dist_nonneg (x := w k) (y := o k)
      linarith
  have hsc : two_facility_cost x p i o ≤ two_facility_social_cost x p o := by
    rw [two_facility_social_cost]
    exact Finset.single_le_sum (fun a _ => two_facility_cost_nonneg x p a o) (Finset.mem_univ i)
  have hsplit_w : two_facility_social_cost x p w =
      two_facility_cost x p i w + ∑ a ∈ Finset.univ.erase i, two_facility_cost x p a w := by
    rw [two_facility_social_cost]
    exact (Finset.add_sum_erase Finset.univ (fun a => two_facility_cost x p a w) (Finset.mem_univ i)).symm
  have hsplit_o : two_facility_social_cost x p o =
      two_facility_cost x p i o + ∑ a ∈ Finset.univ.erase i, two_facility_cost x p a o := by
    rw [two_facility_social_cost]
    exact (Finset.add_sum_erase Finset.univ (fun a => two_facility_cost x p a o) (Finset.mem_univ i)).symm
  have hbound : two_facility_social_cost x p w ≤
      two_facility_social_cost x p o
        + ((Finset.univ.erase i).card : ℝ) * dist (w k) (o k) := by
    rw [hsplit_w, hsplit_o]
    have h1 : two_facility_cost x p i w + ∑ a ∈ Finset.univ.erase i, two_facility_cost x p a w
        ≤ two_facility_cost x p i o + ∑ a ∈ Finset.univ.erase i,
            (two_facility_cost x p a o + dist (w k) (o k)) := by
      apply add_le_add hA
      exact Finset.sum_le_sum (fun a _ => hper a)
    have h2 : two_facility_cost x p i o + ∑ a ∈ Finset.univ.erase i,
            (two_facility_cost x p a o + dist (w k) (o k))
        = (two_facility_cost x p i o + ∑ a ∈ Finset.univ.erase i, two_facility_cost x p a o)
            + ((Finset.univ.erase i).card : ℝ) * dist (w k) (o k) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    linarith [h1, h2]
  have hn : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hcard : ((Finset.univ.erase i).card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Nat.cast_sub hn]
    norm_num
  have hnonneg : (0:ℝ) ≤ (Fintype.card ι : ℝ) - 1 := by
    have : (1:ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hn
    linarith
  have hstep1 : ((Finset.univ.erase i).card : ℝ) * dist (w k) (o k)
      ≤ ((Fintype.card ι : ℝ) - 1) * (2 * two_facility_cost x p i o) := by
    rw [hcard]
    exact mul_le_mul_of_nonneg_left hD hnonneg
  have hstep2 : ((Fintype.card ι : ℝ) - 1) * (2 * two_facility_cost x p i o)
      ≤ ((Fintype.card ι : ℝ) - 1) * (2 * two_facility_social_cost x p o) := by
    apply mul_le_mul_of_nonneg_left _ hnonneg
    linarith [hsc]
  have hfinal : two_facility_social_cost x p o
      + ((Fintype.card ι : ℝ) - 1) * (2 * two_facility_social_cost x p o)
      = (2 * (Fintype.card ι : ℝ) - 1) * two_facility_social_cost x p o := by ring
  linarith [hbound, hstep1, hstep2, hfinal]
