import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TT
import AFTD.Kb.GameTheoryEconomics.TTtostdSimplex
import AFTD.Kb.GameTheoryEconomics.TTFinite
import AFTD.Kb.GameTheoryEconomics.TTInhabited
import AFTD.Kb.GameTheoryEconomics.TTFunlike

/-!
# TT.CoestdSimplex

Topic: general_equilibrium   Node: 413656a962ec

Provenance: formalization of a published result. Source: EconCSLib, `TT.CoestdSimplex`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TT.CoestdSimplex
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
variable (n l : ℕ+) (i : Fin n) in
noncomputable instance TT.CoestdSimplex : CoeOut (TT n l) (stdSimplex ℝ (Fin n)) where
  coe := TTtostdSimplex
