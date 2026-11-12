import AFTD.Prelude
import AFTD.Kb.Tcs.PptQutritBellVector
import AFTD.Kb.Tcs.PptQutritSteeredNormalizer
import AFTD.Kb.Tcs.PptQutritBellSourceFullRankOnEveryPlane
import AFTD.Kb.Tcs.RankTwoQutritProjectionIsometry
import AFTD.Kb.Tcs.PptQutritSourceProjectionBasisFromIsometryFactor

/-!
# ppt_qutrit_source_projection_basis_full_rank

Topic: quantum   Node: 04dbd543a002

Provenance: helper lemma. Source-specific basis-selection helper for OP-693; see https://arxiv.org/abs/1405.4502.

Every rank-two qutrit projection admits an orthonormal basis whose first normalized-source contraction has full row rank.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder

theorem ppt_qutrit_source_projection_basis_full_rank :
  ∀ P : Matrix (Fin 3) (Fin 3) ℂ, P.IsHermitian → P*P=P → P.rank=2 →
    ∃ U : Matrix (Fin 3) (Fin 2) ℂ,
      Uᴴ*U=1 ∧ U*Uᴴ=P ∧
      (let W : Matrix (Fin 3) (Fin 2) ℂ := ppt_qutrit_steered_normalizer * U
       let lam : Fin 4 → ℝ := fun t => if t = 0 then 3257/6884 else if t = 3 then 27/6884 else 450/1721
       let G : Matrix (Fin 3) (Fin 4) ℂ := fun i t =>
        (Real.sqrt (lam t) : ℂ) * (∑ x : Fin 3, star (W x 0) * ppt_qutrit_bell_vector t (i,x))
       G.rank=3) := ppt_qutrit_source_projection_basis_from_isometry_factor rank_two_qutrit_projection_isometry
