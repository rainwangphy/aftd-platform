import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TT
import AFTD.Kb.GameTheoryEconomics.TTFinite
import AFTD.Kb.GameTheoryEconomics.TTInhabited

/-!
# TT.funlike

Topic: general_equilibrium   Node: 385e591bea0a

Provenance: formalization of a published result. Source: EconCSLib, `TT.funlike`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

TT.funlike
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
variable (n l : ℕ+) (i : Fin n) in
noncomputable instance TT.funlike : FunLike (TT n l) (Fin n) (Fin (l+1)) where
  coe := fun a => a.1
  coe_injective := Subtype.val_injective
