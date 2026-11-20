import AFTD.Prelude
import AFTD.Kb.Tcs.Op874PairRichFixedWordsKernelData

/-!
# op874_fixed_words_proper_and_pair_rich

Topic: graphs   Node: 4281003d9766

Provenance: helper lemma. Fixed-high matching-factor obstruction, experiment 36048.

The two displayed five-cycle edge words are proper, and the two factor colors at the endpoints of every prescribed matching edge form unequal unordered pairs.
-/

theorem op874_fixed_words_proper_and_pair_rich :
    (∀ (s : Bool) (i : Fin 5), In1098Bit.word s (i - 1) ≠ In1098Bit.word s i) ∧
    (∀ i : Fin 5, let j := In1098Bit.perm i;
      ¬ ((In1098Bit.word false (i-1) = In1098Bit.word true (j-1) ∧
          In1098Bit.word false i = In1098Bit.word true j) ∨
         (In1098Bit.word false (i-1) = In1098Bit.word true j ∧
          In1098Bit.word false i = In1098Bit.word true (j-1)))) := by decide
