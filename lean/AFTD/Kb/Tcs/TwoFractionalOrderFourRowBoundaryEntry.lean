import AFTD.Prelude
import AFTD.Kb.Tcs.IsStandardizedLaplacianTwoFractional
import AFTD.Kb.Tcs.IsStandardizedLaplacian

/-!
# two_fractional_order_four_row_boundary_entry

Topic: graphs   Node: 2a893cd53f61

Provenance: helper lemma. step towards standardized_laplacian_order_four_two_fractional_im_le

Every row of an order-4 standardized Laplacian with at most two strictly fractional off-diagonal entries has an off-diagonal entry equal to 0 or to -1/4 (i.e. on the boundary of the range [-1/4, 0]).
-/

/-- In a two-fractional order-4 standardized Laplacian each row has an off-diagonal entry at 0 or -1/4. -/
theorem two_fractional_order_four_row_boundary_entry (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : is_standardized_laplacian_two_fractional 4 L) (i : Fin 4) :
    ∃ j : Fin 4, j ≠ i ∧ (L i j = 0 ∨ L i j = -(1 : ℝ) / 4) := by
  by_contra h
  simp only [not_exists, not_and, not_or] at h
  set S : Finset (Fin 4) :=
    Finset.univ.filter (fun j : Fin 4 => j ≠ i ∧ -1 / ((4:ℕ):ℝ) < L i j ∧ L i j < 0) with hS
  have hScard : S.card ≤ 2 := by
    have h := hL.2 i
    simpa only [hS, Nat.cast_ofNat] using h
  have hsub : Finset.univ.erase i ⊆ S := by
    intro j hj
    rw [Finset.mem_erase] at hj
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ j, hj.1, ?_, ?_⟩
    · exact lt_of_le_of_ne (hL.1.2 i j hj.1.symm).1 (fun hh => (h j hj.1).2 (by rw [← hh]; norm_num))
    · exact lt_of_le_of_ne (hL.1.2 i j hj.1.symm).2 (fun hh => (h j hj.1).1 hh)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ] at hc
  simp only [Fintype.card_fin] at hc
  omega
