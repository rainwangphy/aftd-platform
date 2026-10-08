import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TT
import AFTD.Kb.GameTheoryEconomics.TTFinite

/-!
# TT.inhabited

Topic: general_equilibrium   Node: 2a02eb844974

Provenance: formalization of a published result. Source: EconCSLib, `TT.inhabited`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

TT.inhabited
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
variable (n l : ℕ+) (i : Fin n) in
noncomputable instance TT.inhabited : Inhabited (TT n l) where
  default :=
    ⟨ fun i => if i = 0 then Fin.last l else 0,  by
      show ∑ j : Fin n, ((if j = 0 then Fin.last l else 0 : Fin (l+1)) : ℕ) = l
      rw [Finset.sum_eq_single (0 : Fin n)]
      · simp
      · intro b _ hb; simp [hb]
      · simp [Fin.val_last] ⟩
