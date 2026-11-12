import AFTD.Prelude
import AFTD.Kb.Tcs.PptQutritBellVector
import AFTD.Kb.Tcs.PptQutritSteeredNormalizer
import AFTD.Kb.Tcs.PptQutritSourceProjectionBasisFromIsometryFactor
import AFTD.Kb.Tcs.RankTwoQutritProjectionIsometry
import AFTD.Kb.Tcs.PptQutritSourceNormalizedGramIfThreeLemmas
import AFTD.Kb.Tcs.PptQutritBellStatePartialTransposeInvariant
import AFTD.Kb.Tcs.RealPositiveQutritGramNormalizer

/-!
# ppt_qutrit_source_normalized_gram_for_plane

Topic: quantum   Node: 3e933bd564bf

Provenance: helper lemma. Source-specific helper for OP-693; see https://arxiv.org/abs/1405.4502.

For every rank-two qutrit projection, a suitable plane basis and real first-factor filter normalize the compressed four-vector source while preserving partial-transpose invariance.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder

theorem ppt_qutrit_source_normalized_gram_for_plane :
  ∀ P : Matrix (Fin 3) (Fin 3) ℂ, P.IsHermitian → P*P=P → P.rank=2 →
    ∃ (U : Matrix (Fin 3) (Fin 2) ℂ) (F : Matrix (Fin 3 × Fin 2) (Fin 4) ℂ)
      (T : Matrix (Fin 3) (Fin 3) ℂ),
      Uᴴ*U=1 ∧ U*Uᴴ=P ∧
      (let V : Matrix (Fin 3) (Fin 4) ℂ := fun i t => F (i,0) t; V*Vᴴ=1) ∧
      (∀ i j : Fin 3, ∀ p q : Fin 2, (F*Fᴴ) (i,p) (j,q) = (F*Fᴴ) (j,p) (i,q)) ∧
      (let W : Matrix (Fin 3) (Fin 2) ℂ := ppt_qutrit_steered_normalizer * U
       let lam : Fin 4 → ℝ := fun t => if t = 0 then 3257/6884 else if t = 3 then 27/6884 else 450/1721
       ∀ i : Fin 3, ∀ p : Fin 2, ∀ t : Fin 4,
        (Real.sqrt (lam t) : ℂ) * (∑ x : Fin 3, star (W x p) * ppt_qutrit_bell_vector t (i,x)) =
          ∑ a : Fin 3, T i a * F (a,p) t) := by
  exact ppt_qutrit_source_normalized_gram_if_three_lemmas
    (ppt_qutrit_source_projection_basis_from_isometry_factor rank_two_qutrit_projection_isometry)
    ppt_qutrit_bell_state_partial_transpose_invariant
    real_positive_qutrit_gram_normalizer
