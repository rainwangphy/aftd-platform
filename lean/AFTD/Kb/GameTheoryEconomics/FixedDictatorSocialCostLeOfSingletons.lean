import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCost
import AFTD.Kb.GameTheoryEconomics.TwoFacilitySocialCost
import AFTD.Kb.GameTheoryEconomics.IsTwoFacilityFeasible
import AFTD.Kb.GameTheoryEconomics.IsClosestCandidate
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCostNonneg

/-!
# fixed_dictator_social_cost_le_of_singletons

Topic: mechanism_design   Node: d7932a26d83f

Provenance: helper lemma. Case 2 of the proof of Theorem 4.5 of arXiv:2610.18006 (Truthful two-facility location with candidate locations in metric spaces); serves fixed_dictator_social_cost_le

Case 2 of Theorem 4.5: with no agent approving both facilities, if F_1 is at a closest candidate w_1 of an agent i approving F_1 and F_2 at a closest available candidate w_2 (≠ w_1) of an agent j approving F_2, then SC(w) ≤ (2n-1) SC(o) for every feasible o.
-/

theorem fixed_dictator_social_cost_le_of_singletons {ι X : Type*} [Fintype ι] [MetricSpace X] [DecidableEq X]
    (C : Finset X) (x : ι → X) (p : ι → Fin 2 → Bool)
    (hnd : ∀ a, ¬ (p a 0 = true ∧ p a 1 = true)) (w : Fin 2 → X) (i j : ι)
    (hi : p i 0 = true) (hj : p j 1 = true)
    (hw0 : IsClosestCandidate C (x i) (w 0)) (hw1 : IsClosestCandidate (C.erase (w 0)) (x j) (w 1))
    (o : Fin 2 → X) (ho : IsTwoFacilityFeasible C o) :
    two_facility_social_cost x p w ≤ (2 * (Fintype.card ι : ℝ) - 1) * two_facility_social_cost x p o := by
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
  have hij : i ≠ j := by
    rintro rfl; rw [hi] at hj0; exact Bool.noConfusion hj0
  have cost_eq : ∀ a (c : Fin 2 → X), two_facility_cost x p a c =
      (if p a 0 then dist (x a) (c 0) else 0) + (if p a 1 then dist (x a) (c 1) else 0) := by
    intro a c; simp [two_facility_cost, Fin.sum_univ_two]
  have cost_nonneg : ∀ a (c : Fin 2 → X), 0 ≤ two_facility_cost x p a c := by
    intro a c; rw [cost_eq]
    apply add_nonneg <;> split_ifs <;> simp [dist_nonneg]
  set ci := dist (x i) (o 0) with hci
  set cj := dist (x j) (o 1) with hcj
  have hci' : two_facility_cost x p i o = ci := by rw [cost_eq]; simp [hi, hi1, hci]
  have hcj' : two_facility_cost x p j o = cj := by rw [cost_eq]; simp [hj, hj0, hcj]
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
  -- per agent
  have hper : ∀ a, two_facility_cost x p a w ≤ two_facility_cost x p a o + E := by
    intro a
    rw [cost_eq, cost_eq]
    have hE0 : 0 ≤ E := by positivity
    cases h0 : p a 0 <;> cases h1 : p a 1
    · simp; exact hE0
    · simp
      have := dist_triangle (x a) (o 1) (w 1)
      linarith
    · simp
      have := dist_triangle (x a) (o 0) (w 0)
      linarith
    · exact absurd ⟨h0, h1⟩ (hnd a)
  have hself : two_facility_cost x p i w ≤ two_facility_cost x p i o := by
    rw [cost_eq, hci']; simp [hi, hi1]; exact hi_w0
  -- sum
  unfold two_facility_social_cost
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ (fun a => two_facility_cost x p a o) (Finset.mem_univ i)]
  have hsum : ∑ a ∈ Finset.univ.erase i, two_facility_cost x p a w ≤
      ∑ a ∈ Finset.univ.erase i, two_facility_cost x p a o + ((Fintype.card ι : ℝ) - 1) * E := by
    have := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ.erase i) => hper a)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, nsmul_eq_mul] at this
    have hn1 : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.2 ⟨i⟩
    rw [Nat.cast_sub hn1] at this
    simpa using this
  have hpair : ci + cj ≤ two_facility_cost x p i o + ∑ a ∈ Finset.univ.erase i, two_facility_cost x p a o := by
    rw [hci', ← hcj']
    have : two_facility_cost x p j o ≤ ∑ a ∈ Finset.univ.erase i, two_facility_cost x p a o :=
      Finset.single_le_sum (fun a _ => cost_nonneg a o) (Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ j⟩)
    linarith
  have hn1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos_iff.2 ⟨i⟩
  have hrest : 0 ≤ ∑ a ∈ Finset.univ.erase i, two_facility_cost x p a o :=
    Finset.sum_nonneg (fun a _ => cost_nonneg a o)
  nlinarith [hsum, hpair, hself, hn1, hci0, hcj0]
