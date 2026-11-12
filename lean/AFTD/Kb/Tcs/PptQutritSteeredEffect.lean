import AFTD.Prelude
import AFTD.Kb.Tcs.PptQutritSteeredUnnormalizedEffect
import AFTD.Kb.Tcs.PptQutritSteeredNormalizer

/-!
# ppt_qutrit_steered_effect

Topic: quantum   Node: 8addb88b6f8e

Provenance: helper lemma. Helper for OP-693 from arXiv:1405.4502, equations (1), (2), (5); and arXiv:2010.04048, Appendix A.

The normalized steered effects obtained from the explicit PPT Bell example.
-/

open Matrix
open scoped BigOperators ComplexOrder

noncomputable def ppt_qutrit_steered_effect (j : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ := ppt_qutrit_steered_normalizer * ppt_qutrit_steered_unnormalized_effect j * ppt_qutrit_steered_normalizer
