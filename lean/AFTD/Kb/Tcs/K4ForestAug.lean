import AFTD.Prelude
import AFTD.Kb.Tcs.K4Forest

/-!
# k4_forest_aug

Topic: combinatorics   Node: fc54cf87c151

Provenance: helper lemma. step towards matroid_common_list_colorable_two_not_of_colorable_two (arXiv:2610.07318 (A note on the list chromatic number of two matroids), Theorem 1.1)

The forests of K₄ satisfy the matroid augmentation axiom.
-/

set_option maxRecDepth 100000 in
theorem k4_forest_aug : ∀ ⦃I J : Finset (Fin 6)⦄, k4_forest I → k4_forest J → I.card < J.card →
    ∃ e ∈ J, e ∉ I ∧ k4_forest (insert e I) := by
  have key : ∀ I J : Finset (Fin 6),
      (decide (I.card ≤ 3) && I != {0, 2, 5} && I != {0, 3, 4} && I != {1, 2, 4} && I != {1, 3, 5}) = true →
      (decide (J.card ≤ 3) && J != {0, 2, 5} && J != {0, 3, 4} && J != {1, 2, 4} && J != {1, 3, 5}) = true →
      decide (I.card < J.card) = true →
      (J.filter fun e => e ∉ I ∧ (decide ((insert e I).card ≤ 3) && insert e I != {0, 2, 5} &&
        insert e I != {0, 3, 4} && insert e I != {1, 2, 4} && insert e I != {1, 3, 5}) = true).Nonempty := by
    decide +kernel
  intro I J hI hJ hlt
  obtain ⟨e, he⟩ := key I J (by simpa [k4_forest, and_assoc] using hI) (by simpa [k4_forest, and_assoc] using hJ)
    (by simpa using hlt)
  simp only [Finset.mem_filter] at he
  refine ⟨e, he.1, he.2.1, ?_⟩
  have := he.2.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
  simp only [k4_forest]
  tauto
