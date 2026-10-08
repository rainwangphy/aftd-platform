import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TT
import AFTD.Kb.GameTheoryEconomics.TTtostdSimplex
import AFTD.Kb.GameTheoryEconomics.StdSimplexPick
import AFTD.Kb.GameTheoryEconomics.TTFinite
import AFTD.Kb.GameTheoryEconomics.TTInhabited
import AFTD.Kb.GameTheoryEconomics.TTFunlike
import AFTD.Kb.GameTheoryEconomics.TTCoestdSimplex
import AFTD.Kb.GameTheoryEconomics.TTIST
import AFTD.Kb.GameTheoryEconomics.TTILO

/-!
# Fcolor

Topic: general_equilibrium   Node: ff74ab30b763

Provenance: formalization of a published result. Source: EconCSLib, `Fcolor`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fcolor
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
variable (n l : ℕ+) (i : Fin n) in
set_option quotPrecheck false in
variable (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n)) in
variable {n l} in
noncomputable def Fcolor (x : TT n l) : Fin n := stdSimplex.pick x (f x)
