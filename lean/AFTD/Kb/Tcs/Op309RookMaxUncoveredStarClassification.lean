import AFTD.Prelude
import AFTD.Kb.Tcs.Op309RookUncoveredCount
import AFTD.Kb.Tcs.Op309K33WitnessMinDegree

/-!
# op309_rook_max_uncovered_star_classification

Topic: graphs   Node: ba32786d704e

Provenance: helper lemma. OP-309 six-vertex maximum-uncovered obstruction, experiment 40722.

Every totally edge-dominating set leaving two vertices uncovered in the three-by-three incidence array is a full row or column.
-/

theorem op309_rook_max_uncovered_star_classification
  (R : Finset (Fin 3 × Fin 3))
  (hdom : ∀ e : Fin 3 × Fin 3, ∃ f ∈ R, op309_rook_adj e f)
  (hmax : op309_rook_uncovered_count R = 2) :
  (∃ i : Fin 3, R = Finset.univ.filter fun e : Fin 3 × Fin 3 => e.1 = i) ∨
  (∃ j : Fin 3, R = Finset.univ.filter fun e : Fin 3 × Fin 3 => e.2 = j) := by
  revert R
  decide
