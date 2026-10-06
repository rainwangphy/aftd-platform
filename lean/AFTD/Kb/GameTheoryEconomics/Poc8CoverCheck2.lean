import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8CoverOk

/-!
# poc8_cover_check_2

Topic: fair_division   Node: 2ee55904abb0

Provenance: helper lemma. step towards poc_linkedness_conjecture_counterexample (counterexample to arXiv:1908.05433, Conjecture 3.10; kernel-checked certificate)

Kernel check of the cover condition for all terminal tuples with first terminal x = 2.
-/

theorem poc8_cover_check_2 : ∀ y a b c : Fin 8, poc8_cover_ok 2 y a b c = true := by
  decide +kernel
