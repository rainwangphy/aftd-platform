import AFTD.Prelude
import AFTD.Kb.Tcs.Op874SparsePairRichWordsKernelData
import AFTD.Kb.Tcs.UniquelyK4SaturatedMaxDegreeSixOrderTwelve

/-!
# op874_sparse_words_exactly_one_square_conflict

Topic: graphs   Node: 02bf66a78a45

Provenance: helper lemma. Sparse fixed-high matching-factor obstruction, experiments 36281 and 36285.

Each of the two explicit pentagon high-color words has exactly one distance-two color equality.
-/

theorem op874_sparse_words_exactly_one_square_conflict : ∀ s : Bool, ∃! i : Fin 5, In1098Sparse.word s i = In1098Sparse.word s (i+2) := by decide
