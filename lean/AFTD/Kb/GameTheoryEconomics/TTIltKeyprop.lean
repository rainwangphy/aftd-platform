import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TT
import AFTD.Kb.GameTheoryEconomics.TTFunlike
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.TTILO
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder
import AFTD.Kb.GameTheoryEconomics.TTFinite
import AFTD.Kb.GameTheoryEconomics.TTInhabited
import AFTD.Kb.GameTheoryEconomics.TTCoestdSimplex
import AFTD.Kb.GameTheoryEconomics.TTIST

/-!
# TT.Ilt_keyprop

Topic: general_equilibrium   Node: 4e52b67ec113

Provenance: formalization of a published result. Source: EconCSLib, `TT.Ilt_keyprop`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TT.Ilt_keyprop
-/

set_option quotPrecheck false
local notation  lhs "<[" i "]" rhs => (IndexedLOrder.IST i).lt lhs rhs
local notation  lhs "≤[" i "]" rhs => (IndexedLOrder.IST i).le lhs rhs

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
variable (n l : ℕ+) (i : Fin n) in
set_option quotPrecheck false in
lemma TT.Ilt_keyprop (a b : TT n l) :
  a i < b i → a <[i] b := by
  intro h
  change toLex (a i, a) < toLex (b i, b)
  change Prod.Lex (· < ·) (· < ·) (a i, a) (b i, b)
  exact Prod.Lex.left a b h
