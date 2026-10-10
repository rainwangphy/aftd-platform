import AFTD.Prelude
import AFTD.Kb.Physics.Time

/-!
# Time.instNonempty

Topic: classical_mechanics   Node: 8aeb87e9c983

Provenance: formalization of a published result. Source: Physlib, `Time.instNonempty`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Time.instNonempty
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
noncomputable instance Time.instNonempty : Nonempty Time := ⟨⟨0⟩⟩
