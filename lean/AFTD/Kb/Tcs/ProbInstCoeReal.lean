import AFTD.Prelude
import AFTD.Kb.Tcs.Prob

/-!
# Prob.instCoeReal

Topic: information   Node: ec36faefbbf9

Provenance: formalization of a published result. Source: QuantumInfo, `Prob.instCoeReal`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ClassicalInfo/Prob.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Prob.instCoeReal
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
noncomputable instance Prob.instCoeReal : Coe Prob ℝ := ⟨Subtype.val⟩
