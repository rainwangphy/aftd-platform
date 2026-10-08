import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.PushTowardsZ
import AFTD.Kb.GameTheoryEconomics.TPush
import AFTD.Kb.GameTheoryEconomics.ZUniform
import AFTD.Kb.GameTheoryEconomics.TPushContinuous

/-!
# pushTowardsZ_continuous

Topic: general_equilibrium   Node: 282bc62fa4ec

Provenance: formalization of a published result. Source: EconCSLib, `pushTowardsZ_continuous`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Continuity of `pushTowardsZ card`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Continuity of `pushTowardsZ card`. -/
lemma pushTowardsZ_continuous : Continuous (pushTowardsZ card) := by
  apply Continuous.subtype_mk
  classical
  apply continuous_pi
  intro k
  have hxk : Continuous (fun x : BigSimplex card => x.1 k) :=
    (continuous_apply k).comp continuous_subtype_val
  have hone_minus_t : Continuous (fun x => (1 : ℝ) - tPush card x) :=
    continuous_const.sub (tPush_continuous card)
  have hterm1 : Continuous (fun x => ((1 : ℝ) - tPush card x) * x.1 k) :=
    hone_minus_t.mul hxk
  have hterm2 : Continuous (fun x => (tPush card x) * (z_uniform card).1 k) :=
    (tPush_continuous card).mul continuous_const
  exact hterm1.add hterm2
