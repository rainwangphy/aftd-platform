import AFTD.Prelude

/-!
# SingleParameterMechanism.myersonPayment

Topic: mechanism_design   Node: 3cdac9024d5e

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.myersonPayment`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Myerson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The canonical Myerson payment formula associated with an allocation rule `x`. Holding all other bids fixed, agent `i` pays `bᵢ xᵢ(b) - ∫₀^{bᵢ} xᵢ(z, b₋ᵢ) dz`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} in
/-- The canonical Myerson payment formula associated with an allocation rule `x`. Holding all other bids fixed, agent `i` pays `bᵢ xᵢ(b) - ∫₀^{bᵢ} xᵢ(z, b₋ᵢ) dz`. -/
noncomputable def SingleParameterMechanism.myersonPayment
    [DecidableEq I]
    (x : (I → ℝ) → I → ℝ) (b : I → ℝ) (i : I) : ℝ :=
  b i * x b i - ∫ z in 0..b i, x (Function.update b i z) i
