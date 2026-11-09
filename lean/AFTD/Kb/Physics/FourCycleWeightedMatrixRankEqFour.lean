import AFTD.Prelude
import AFTD.Kb.Physics.CycleWeightedAdjacencyMatrix

/-!
# four_cycle_weighted_matrix_rank_eq_four

Topic: quantum_mechanics   Node: 4cf259e0576f

Provenance: formalization of a published result. Source: arXiv:2610.27080, Section III.1, Eq. (17)

For any field F of characteristic two and any injective function t : Fin 4 → F, the cycle weighted adjacency matrix cycle_weighted_adjacency_matrix 4 t has rank 4.
-/

open scoped CharTwo

lemma four_cycle_weighted_matrix_rank_eq_four_step1
    {F : Type*} [CommRing F] [CharP F 2] (a b c d v1 v3 : F)
    (h0 : (a + b) * v1 + (a + d) * v3 = 0)
    (h2 : (c + b) * v1 + (c + d) * v3 = 0) :
    (a + c) * (v1 + v3) = 0 := by
  have h : (a + c) * (v1 + v3) =
    ((a + b) * v1 + (a + d) * v3) + ((c + b) * v1 + (c + d) * v3) - 2 * (b * v1 + d * v3) := by ring
  rw [h, h0, h2]
  simp

lemma four_cycle_weighted_matrix_rank_eq_four_step2
    {F : Type*} [Field F] [CharP F 2] (a c v1 v3 : F)
    (hac : a ≠ c) (h : (a + c) * (v1 + v3) = 0) : v1 = v3 := by
  have hac_add : a + c ≠ 0 := by
    intro h0
    apply hac
    rwa [CharTwo.add_eq_zero] at h0
  cases mul_eq_zero.mp h with
  | inl h1 => exact (hac_add h1).elim
  | inr h2 => rwa [CharTwo.add_eq_zero] at h2

lemma four_cycle_weighted_matrix_rank_eq_four_step3
    {F : Type*} [Field F] [CharP F 2] (a b d v1 v3 : F)
    (h0 : (a + b) * v1 + (a + d) * v3 = 0)
    (hv : v1 = v3) (hbd : b ≠ d) : v1 = 0 := by
  have hbd_add : b + d ≠ 0 := by
    intro h0'
    apply hbd
    rwa [CharTwo.add_eq_zero] at h0'
  have hid : (b + d) * v1 = 0 := by
    calc (b + d) * v1
      _ = ((a + b) * v1 + (a + d) * v3) - 2 * a * v1 - (a + d) * (v3 - v1) := by ring
      _ = 0 := by rw [h0, hv]; simp
  cases mul_eq_zero.mp hid with
  | inl h1 => exact (hbd_add h1).elim
  | inr h2 => exact h2

/-- For any field of characteristic two and any injective 4-tuple, the weighted adjacency matrix of the 4-cycle has full rank 4. -/
theorem four_cycle_weighted_matrix_rank_eq_four
    {F : Type*} [Field F] [CharP F 2] (t : Fin 4 → F) (hinj : Function.Injective t) :
    (cycle_weighted_adjacency_matrix 4 t).rank = 4 := by
  have ht02 : t 0 ≠ t 2 := by
    intro h
    have : (0 : Fin 4) = 2 := hinj h
    revert this; decide
  have ht13 : t 1 ≠ t 3 := by
    intro h
    have : (1 : Fin 4) = 3 := hinj h
    revert this; decide
  have h_inj : Function.Injective (cycle_weighted_adjacency_matrix 4 t).mulVecLin := by
    intro v w hvw
    have h_sub : (cycle_weighted_adjacency_matrix 4 t).mulVecLin (v - w) = 0 := by
      rw [map_sub, hvw, sub_self]
    have h_zero : (cycle_weighted_adjacency_matrix 4 t).mulVec (v - w) = 0 := h_sub
    have h_ker : ∀ (u : Fin 4 → F), (cycle_weighted_adjacency_matrix 4 t).mulVec u = 0 → u = 0 := by
      intro u hu
      have e0 : (t 0 + t 1) * u 1 + (t 0 + t 3) * u 3 = 0 := by
        have := congr_fun hu 0
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four] at this
        dsimp [cycle_weighted_adjacency_matrix] at this
        have a01 : (SimpleGraph.cycleGraph 4).Adj (0 : Fin 4) 1 := by decide
        have a02 : ¬ (SimpleGraph.cycleGraph 4).Adj (0 : Fin 4) 2 := by decide
        have a03 : (SimpleGraph.cycleGraph 4).Adj (0 : Fin 4) 3 := by decide
        simp [a01, a02, a03] at this
        exact this
      have e1 : (t 1 + t 0) * u 0 + (t 1 + t 2) * u 2 = 0 := by
        have := congr_fun hu 1
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four] at this
        dsimp [cycle_weighted_adjacency_matrix] at this
        have a10 : (SimpleGraph.cycleGraph 4).Adj (1 : Fin 4) 0 := by decide
        have a12 : (SimpleGraph.cycleGraph 4).Adj (1 : Fin 4) 2 := by decide
        have a13 : ¬ (SimpleGraph.cycleGraph 4).Adj (1 : Fin 4) 3 := by decide
        simp [a10, a12, a13] at this
        exact this
      have e2 : (t 2 + t 1) * u 1 + (t 2 + t 3) * u 3 = 0 := by
        have := congr_fun hu 2
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four] at this
        dsimp [cycle_weighted_adjacency_matrix] at this
        have a20 : ¬ (SimpleGraph.cycleGraph 4).Adj (2 : Fin 4) 0 := by decide
        have a21 : (SimpleGraph.cycleGraph 4).Adj (2 : Fin 4) 1 := by decide
        have a23 : (SimpleGraph.cycleGraph 4).Adj (2 : Fin 4) 3 := by decide
        simp [a20, a21, a23] at this
        exact this
      have e3 : (t 3 + t 0) * u 0 + (t 3 + t 2) * u 2 = 0 := by
        have := congr_fun hu 3
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four] at this
        dsimp [cycle_weighted_adjacency_matrix] at this
        have a30 : (SimpleGraph.cycleGraph 4).Adj (3 : Fin 4) 0 := by decide
        have a31 : ¬ (SimpleGraph.cycleGraph 4).Adj (3 : Fin 4) 1 := by decide
        have a32 : (SimpleGraph.cycleGraph 4).Adj (3 : Fin 4) 2 := by decide
        simp [a30, a31, a32] at this
        exact this
      have hu13 : (t 0 + t 2) * (u 1 + u 3) = 0 :=
        four_cycle_weighted_matrix_rank_eq_four_step1 (t 0) (t 1) (t 2) (t 3) (u 1) (u 3) e0 e2
      have hu1_eq_3 : u 1 = u 3 :=
        four_cycle_weighted_matrix_rank_eq_four_step2 (t 0) (t 2) (u 1) (u 3) ht02 hu13
      have hu1_zero : u 1 = 0 :=
        four_cycle_weighted_matrix_rank_eq_four_step3 (t 0) (t 1) (t 3) (u 1) (u 3) e0 hu1_eq_3 ht13
      have hu3_zero : u 3 = 0 := by rw [← hu1_eq_3, hu1_zero]
      have hu02 : (t 1 + t 3) * (u 0 + u 2) = 0 :=
        four_cycle_weighted_matrix_rank_eq_four_step1 (t 1) (t 0) (t 3) (t 2) (u 0) (u 2) e1 e3
      have hu0_eq_2 : u 0 = u 2 :=
        four_cycle_weighted_matrix_rank_eq_four_step2 (t 1) (t 3) (u 0) (u 2) ht13 hu02
      have hu0_zero : u 0 = 0 :=
        four_cycle_weighted_matrix_rank_eq_four_step3 (t 1) (t 0) (t 2) (u 0) (u 2) e1 hu0_eq_2 ht02
      have hu2_zero : u 2 = 0 := by rw [← hu0_eq_2, hu0_zero]
      ext i
      fin_cases i
      · exact hu0_zero
      · exact hu1_zero
      · exact hu2_zero
      · exact hu3_zero
    have h_diff : v - w = 0 := h_ker (v - w) h_zero
    exact sub_eq_zero.mp h_diff
  rw [Matrix.rank, LinearMap.finrank_range_of_inj h_inj]
  simp
