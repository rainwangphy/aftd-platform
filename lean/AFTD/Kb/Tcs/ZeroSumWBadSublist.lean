import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroSumWBad
import AFTD.Kb.Tcs.ZeroSumAdmissible
import AFTD.Kb.Tcs.ZeroSumGoodSubseq

/-!
# zero_sum_w_bad_sublist

Topic: combinatorics   Node: a29ecb6a9c3c

Provenance: helper lemma. step towards zero_sum_w_eq_question

Any sublist of a w-bad sequence is also w-bad.
-/

/-- Any sublist of a w-bad sequence is also w-bad. -/
theorem zero_sum_w_bad_sublist {n r : ℕ} {A B : List (Fin r → ℤ)} (hsub : B.Sublist A) (hbad : zero_sum_w_bad n A) : zero_sum_w_bad n B := by
  constructor
  · intro a ha
    exact hbad.1 a (hsub.subset ha)
  · intro I hI
    obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    let emb := f.toEmbedding
    have hsum : ∀ j, ∑ i ∈ I.map emb, A.get i j = ∑ i ∈ I, B.get i j := by
      intro j
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i _
      exact congr_fun (hf i).symm j
    have hgood : zero_sum_good_subseq n A (I.map emb) := by
      refine ⟨hI.1.map, ?_, ?_⟩
      · intro j
        rw [hsum j]
        exact hI.2.1 j
      · obtain ⟨j, hj⟩ := hI.2.2
        use j
        rw [hsum j]
        exact hj
    exact hbad.2 (I.map emb) hgood
