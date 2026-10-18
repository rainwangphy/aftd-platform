import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCost
import AFTD.Kb.GameTheoryEconomics.TwoFacilitySocialCost
import AFTD.Kb.GameTheoryEconomics.IsTwoFacilityFeasible
import AFTD.Kb.GameTheoryEconomics.IsClosestCandidate
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCostNonneg

/-!
# fixed_dictator_social_cost_le_of_doubleton

Topic: mechanism_design   Node: 0317ae25c877

Provenance: helper lemma. Case 1 of the proof of Theorem 4.5 of arXiv:2610.18006 (Truthful two-facility location with candidate locations in metric spaces); serves fixed_dictator_social_cost_le

Case 1 of Theorem 4.5: if the facilities are at the two closest candidate locations w_1, w_2 of an agent i approving both, then SC(w) ≤ (2n-1) SC(o) for every feasible o.
-/

lemma fixed_dictator_social_cost_le_of_doubleton_aux_triangle
    {ι X : Type*} [MetricSpace X] (x : ι → X) (p : ι → Fin 2 → Bool)
    (a : ι) (c c' : Fin 2 → X) :
    two_facility_cost x p a c ≤ two_facility_cost x p a c' + dist (c 0) (c' 0) + dist (c 1) (c' 1) := by
  unfold two_facility_cost
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  have h0 : (if p a 0 = true then dist (x a) (c 0) else 0)
      ≤ (if p a 0 = true then dist (x a) (c' 0) else 0) + dist (c 0) (c' 0) := by
    split_ifs with h
    · have := dist_triangle (x a) (c' 0) (c 0)
      rw [dist_comm (c' 0) (c 0)] at this
      linarith
    · have := dist_nonneg (x := c 0) (y := c' 0)
      linarith
  have h1 : (if p a 1 = true then dist (x a) (c 1) else 0)
      ≤ (if p a 1 = true then dist (x a) (c' 1) else 0) + dist (c 1) (c' 1) := by
    split_ifs with h
    · have := dist_triangle (x a) (c' 1) (c 1)
      rw [dist_comm (c' 1) (c 1)] at this
      linarith
    · have := dist_nonneg (x := c 1) (y := c' 1)
      linarith
  linarith

theorem fixed_dictator_social_cost_le_of_doubleton {ι X : Type*} [Fintype ι] [MetricSpace X] [DecidableEq X]
    (C : Finset X) (x : ι → X) (p : ι → Fin 2 → Bool)
    (w : Fin 2 → X) (i : ι) (hi0 : p i 0 = true) (hi1 : p i 1 = true)
    (hw0 : IsClosestCandidate C (x i) (w 0)) (hw1 : IsClosestCandidate (C.erase (w 0)) (x i) (w 1))
    (o : Fin 2 → X) (ho : IsTwoFacilityFeasible C o) :
    two_facility_social_cost x p w ≤ (2 * (Fintype.card ι : ℝ) - 1) * two_facility_social_cost x p o := by
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
  have hper : ∀ a, two_facility_cost x p a w ≤
      two_facility_cost x p a o + (dist (w 0) (o 0) + dist (w 1) (o 1)) := by
    intro a
    have := fixed_dictator_social_cost_le_of_doubleton_aux_triangle x p a w o
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
        + ((Finset.univ.erase i).card : ℝ) * (dist (w 0) (o 0) + dist (w 1) (o 1)) := by
    rw [hsplit_w, hsplit_o]
    have h1 : two_facility_cost x p i w + ∑ a ∈ Finset.univ.erase i, two_facility_cost x p a w
        ≤ two_facility_cost x p i o + ∑ a ∈ Finset.univ.erase i,
            (two_facility_cost x p a o + (dist (w 0) (o 0) + dist (w 1) (o 1))) := by
      apply add_le_add hA
      exact Finset.sum_le_sum (fun a _ => hper a)
    have h2 : two_facility_cost x p i o + ∑ a ∈ Finset.univ.erase i,
            (two_facility_cost x p a o + (dist (w 0) (o 0) + dist (w 1) (o 1)))
        = (two_facility_cost x p i o + ∑ a ∈ Finset.univ.erase i, two_facility_cost x p a o)
            + ((Finset.univ.erase i).card : ℝ) * (dist (w 0) (o 0) + dist (w 1) (o 1)) := by
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
  have hstep1 : ((Finset.univ.erase i).card : ℝ) * (dist (w 0) (o 0) + dist (w 1) (o 1))
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
