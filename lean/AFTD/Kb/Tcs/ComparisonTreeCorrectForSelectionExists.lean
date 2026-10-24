import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTreeCorrectForSelection
import AFTD.Kb.Tcs.ComparisonTree
import AFTD.Kb.Tcs.ComparisonTreeEval
import AFTD.Kb.Tcs.IsLinearExtension

/-!
# comparison_tree_correct_for_selection_exists

Topic: algorithms   Node: e13339d0c3e1

Provenance: helper lemma. arXiv:2610.18740 Section 5

For every natural number n, strict partial order P on Fin n, and rank 1 ≤ i ≤ n, there exists a comparison decision tree on n elements that correctly selects the i-th smallest element for P.
-/

/-- For any partial order and valid rank, there exists a comparison tree correctly selecting that rank. -/
theorem comparison_tree_correct_for_selection_exists {n : ℕ}
    (P : PartialOrder (Fin n)) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ n) :
    ∃ T : ComparisonTree n, comparison_tree_correct_for_selection n P i T := by
  have hr : i - 1 < n := by omega
  refine ⟨ComparisonTree.leaf ⟨i - 1, hr⟩, ?_⟩
  intro L hL
  have heval : comparison_tree_eval (fun a : Fin n => a) (ComparisonTree.leaf (⟨i - 1, hr⟩ : Fin n)) = ⟨i - 1, hr⟩ := by
    simp [comparison_tree_eval]
  rw [heval]
  have hcard : (Finset.univ.filter (fun x : Fin n => x < (⟨i - 1, hr⟩ : Fin n))).card = (⟨i - 1, hr⟩ : Fin n).val := by
    have hset : (Finset.univ.filter (fun x : Fin n => x < (⟨i - 1, hr⟩ : Fin n))) =
        @Finset.Iio (Fin n) (@PartialOrder.toPreorder (Fin n) (@Fin.instPartialOrder n))
          (Fin.instLocallyFiniteOrderBot n) (⟨i - 1, hr⟩ : Fin n) := by
      ext x
      simp [Finset.mem_Iio]
    rw [hset, @Fin.card_Iio n (⟨i - 1, hr⟩ : Fin n)]
  change (Finset.univ.filter (fun x : Fin n => x < (⟨i - 1, hr⟩ : Fin n))).card = i - 1
  rw [hcard]
