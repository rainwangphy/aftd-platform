import AFTD.Prelude
import AFTD.Kb.Tcs.Cells

/-!
# Cells.instZero

Topic: algorithms   Node: d3f907a1d16a

Provenance: formalization of a published result. Source: EconCSLib, `Cells.instZero`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Cells.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cells.instZero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSimpArgs false in
instance Cells.instZero : Zero Cells := ⟨⟨0, 0, le_refl _, le_refl _⟩⟩
