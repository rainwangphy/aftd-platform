import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.TT
import AFTD.Kb.GameTheoryEconomics.TTIlt
import AFTD.Kb.GameTheoryEconomics.TTIST
import AFTD.Kb.GameTheoryEconomics.TTFunlike
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder
import AFTD.Kb.GameTheoryEconomics.TTFinite
import AFTD.Kb.GameTheoryEconomics.TTInhabited
import AFTD.Kb.GameTheoryEconomics.TTCoestdSimplex

/-!
# TT.ILO

Topic: general_equilibrium   Node: 3d64774e0db8

Provenance: formalization of a published result. Source: EconCSLib, `TT.ILO`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TT.ILO
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
variable (n l : ℕ+) (i : Fin n) in
variable {n l} in
noncomputable instance TT.ILO : IndexedLOrder (Fin n) (TT n l) where
  IST := fun i => linearOrderOfSTO (TT.Ilt i)
