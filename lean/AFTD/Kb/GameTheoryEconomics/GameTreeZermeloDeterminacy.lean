import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeValue0
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeValue0OfIVariantZero
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValue0LeOutcomeOfIVariantOne
import AFTD.Kb.GameTheoryEconomics.GameTreeIVariant
import AFTD.Kb.GameTheoryEconomics.GameTreeOptStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcome
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSum
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons

/-!
# GameTree.zermelo_determinacy

Topic: equilibria   Node: ccd4a713a3ee

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.zermelo_determinacy`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Zermelo's theorem (determinacy / saddle value).** In a finite two-player zero-sum perfect-information game, `optStrategy` is a saddle point with value `value₀ g`: * playing `optStrategy`, player 0 *secures* at least `value₀ g` against every opponent play (`1`-variant); * playing `optStrategy`, player 1 *holds* player 0 to at most `value₀ g` against every opponent play (`0`-variant). Hence the game is determined and `value₀ g` is its value, attained by the pure backward-induction strategy on both sides.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- **Zermelo's theorem (determinacy / saddle value).** In a finite two-player zero-sum perfect-information game, `optStrategy` is a saddle point with value `value₀ g`: * playing `optStrategy`, player 0 *secures* at least `value₀ g` against every opponent play (`1`-variant); * playing `optStrategy`, player 1 *holds* player 0 to at most `value₀ g` against every opponent play (`0`-variant). Hence the game is determined and `value₀ g` is its value, attained by the pure backward-induction strategy on both sides. -/
theorem GameTree.zermelo_determinacy (g : GameTree (Fin 2) ℚ) (hzs : IsZeroSum g) :
    (∀ σ' : Strategy (Fin 2) ℚ, IVariant (1 : Fin 2) optStrategy σ' →
        value₀ g ≤ outcome σ' g 0) ∧
    (∀ σ' : Strategy (Fin 2) ℚ, IVariant (0 : Fin 2) optStrategy σ' →
        outcome σ' g 0 ≤ value₀ g) :=
  ⟨fun _ hiv => value₀_le_outcome_of_iVariant_one g hzs hiv,
   fun _ hiv => outcome_le_value₀_of_iVariant_zero g hiv⟩
