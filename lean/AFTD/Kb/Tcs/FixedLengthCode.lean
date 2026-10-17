import AFTD.Prelude
import AFTD.Kb.Tcs.Code

/-!
# FixedLengthCode

Topic: information   Node: 587abe738ba9

Provenance: formalization of a published result. Source: QuantumInfo, `FixedLengthCode`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ClassicalInfo/Capacity.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A `FixedLengthCode` is a `Code` whose output lengths don't depend on the input content, only the input length.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (A I O : Type*) in
/-- A `FixedLengthCode` is a `Code` whose output lengths don't depend on the input content, only the input length. -/
structure FixedLengthCode extends Code A I O where
  enc_length : ℕ → ℕ
  enc_maps_length : ∀ as, (encoder as).length = enc_length (as.length)
  dec_length : ℕ → ℕ
  dec_maps_length : ∀ is, (decoder is).length = dec_length (is.length)
