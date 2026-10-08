import AFTD.Prelude

/-!
# SingleParameterMechanism.ZeroNormalized

Topic: mechanism_design   Node: ac672d4a764d

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.ZeroNormalized`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Myerson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Zero normalization for payment rules: reporting `0` yields payment `0`, holding the other reports fixed.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} in
/-- Zero normalization for payment rules: reporting `0` yields payment `0`, holding the other reports fixed. -/
def SingleParameterMechanism.ZeroNormalized [DecidableEq I] (p : (I → ℝ) → I → ℝ) : Prop :=
  ∀ (i : I) (b : I → ℝ), p (Function.update b i 0) i = 0
