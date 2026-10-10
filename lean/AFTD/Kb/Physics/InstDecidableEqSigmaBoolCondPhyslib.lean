import AFTD.Prelude

/-!
# instDecidableEqSigmaBoolCond_physlib

Topic: classical_mechanics   Node: 9a19ec0046d7

Provenance: formalization of a published result. Source: Physlib, `instDecidableEqSigmaBoolCond_physlib`. Lean proof by Gordon Hsu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/SchurTriangulation.lean (Copyright (c) 2025 Gordon Hsu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type family parameterized by `Bool` has decidable equality if each type variant is decidable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped InnerProductSpace in
open Module in
/-- The type family parameterized by `Bool` has decidable equality if each type variant is decidable. -/
instance instDecidableEqSigmaBoolCond_physlib [DecidableEq m] [DecidableEq n] : DecidableEq (Σ b, cond b m n)
  | ⟨true, _⟩, ⟨false, _⟩
  | ⟨false, _⟩, ⟨true, _⟩ => isFalse nofun
  | ⟨false, i⟩, ⟨false, j⟩
  | ⟨true, i⟩, ⟨true, j⟩ =>
    if h : i = j then isTrue (Sigma.eq rfl h) else isFalse fun | rfl => h rfl
