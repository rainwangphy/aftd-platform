import AFTD.Prelude
import AFTD.Kb.Tcs.Op874SparsePairRichWordsKernelData

/-!
# op874_sparse_words_proper_and_pair_rich

Topic: graphs   Node: 19ffd093d01c

Provenance: helper lemma. Sparse fixed-high matching-factor obstruction, experiments 36281 and 36285.

The sparse fixed factor words are proper and matching endpoint color pairs are unequal.
-/

theorem op874_sparse_words_proper_and_pair_rich :
    (∀ (s : Bool) (i : Fin 5), In1098Sparse.word s (i - 1) ≠ In1098Sparse.word s i) ∧
    (∀ i : Fin 5, let j := In1098Sparse.perm i;
      ¬ ((In1098Sparse.word false (i-1) = In1098Sparse.word true (j-1) ∧
          In1098Sparse.word false i = In1098Sparse.word true j) ∨
         (In1098Sparse.word false (i-1) = In1098Sparse.word true j ∧
          In1098Sparse.word false i = In1098Sparse.word true (j-1)))) := by decide
