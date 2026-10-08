import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TT
import AFTD.Kb.GameTheoryEconomics.TTIlt
import AFTD.Kb.GameTheoryEconomics.TTFunlike
import AFTD.Kb.GameTheoryEconomics.TTFinite
import AFTD.Kb.GameTheoryEconomics.TTInhabited
import AFTD.Kb.GameTheoryEconomics.TTCoestdSimplex

/-!
# TT.IST

Topic: general_equilibrium   Node: c3977546fd2d

Provenance: formalization of a published result. Source: EconCSLib, `TT.IST`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TT.IST
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
variable (n l : ℕ+) (i : Fin n) in
noncomputable instance TT.IST : IsStrictTotalOrder (TT n l) (TT.Ilt i) where
  trichotomous := by
    intro a b h_ab h_ba
    unfold TT.Ilt at h_ab h_ba
    have h_eq :
        toLex (a i, a) = toLex (b i, b) :=
      le_antisymm (le_of_not_gt h_ba) (le_of_not_gt h_ab)
    have h_pair : (a i, a) = (b i, b) :=
      (EquivLike.injective (toLex : (Fin (l + 1) × TT n l) ≃
        Lex (Fin (l + 1) × TT n l))) h_eq
    exact congrArg Prod.snd h_pair
  irrefl := by
    intro a
    unfold TT.Ilt
    exact lt_irrefl _
  trans := by
    intro a b c h_ab h_bc
    unfold TT.Ilt at *
    exact lt_trans h_ab h_bc
