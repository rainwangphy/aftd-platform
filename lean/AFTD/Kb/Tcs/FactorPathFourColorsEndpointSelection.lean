import AFTD.Prelude
import AFTD.Kb.Tcs.PathSelectionOfNoCommonColor

/-!
# factor_path_four_colors_endpoint_selection

Topic: graphs   Node: 001548fbd054

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

If every one of four colors occurs among the two excluded colors at some path vertex, the complementary equal-size palettes admit compatible selection with arbitrary prescribed endpoint colors.
-/

theorem factor_path_four_colors_endpoint_selection
    (a b : ℕ → Fin 4) (n : ℕ)
    (hcard : ∀ i, (Finset.univ \ ({a i, b i} : Finset (Fin 4))).card =
      (Finset.univ \ ({a (i+1), b (i+1)} : Finset (Fin 4))).card)
    (hcover : ∀ z : Fin 4, ∃ i ≤ n, z = a i ∨ z = b i)
    (x y : Fin 4)
    (hx : x ∈ Finset.univ \ ({a 0, b 0} : Finset (Fin 4)))
    (hy : y ∈ Finset.univ \ ({a n, b n} : Finset (Fin 4))) :
    ∃ g : ℕ → Fin 4, g 0 = x ∧ g n = y ∧
      (∀ i ≤ n, g i ∈ Finset.univ \ ({a i, b i} : Finset (Fin 4))) ∧
      (∀ i < n, g (i+1) ∈ Finset.univ \ ({a i, b i} : Finset (Fin 4)) →
        g (i+1) = g i) := by
  apply path_selection_of_no_common_color (fun i => Finset.univ \ ({a i, b i} : Finset (Fin 4))) hcard n x y hx hy
  intro z
  obtain ⟨i, hi, ha | hb⟩ := hcover z
  · refine ⟨i, hi, ?_⟩
    simp [ha]
  · refine ⟨i, hi, ?_⟩
    simp [hb]
