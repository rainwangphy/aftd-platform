import AFTD.Prelude
import AFTD.Kb.Tcs.BigIdx
import AFTD.Kb.Tcs.MidIdx

/-!
# assoc_equiv

Topic: quantum   Node: 28797a5a3096

Provenance: formalization of a published result. Source: QuantumInfo, `assoc_equiv`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Entropy/SSA.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The associator equivalence (no swap needed). Maps (((dA×dB)×dB)×(dB×dC)) to ((dA×dB)×(dB×(dB×dC))).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {d d₁ d₂ d₃ m n : Type*} in
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃] [Fintype m] [Fintype n] in
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃] [DecidableEq m] [DecidableEq n] in
variable {dA dB dC dA₁ dA₂ : Type*} in
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂] in
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂] in
variable {𝕜 : Type*} [RCLike 𝕜] in
variable {α : ℝ} in
open scoped InnerProductSpace RealInnerProductSpace Kronecker Matrix in
open scoped MatrixOrder ComplexOrder in
open scoped MatrixOrder in
variable {dA dB dC : Type*} [Fintype dA] [Fintype dB] [Fintype dC] in
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] in
variable {dA dB dC : Type*} [Fintype dA] [Fintype dB] [Fintype dC] in
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] in
/-- The associator equivalence (no swap needed). Maps (((dA×dB)×dB)×(dB×dC)) to ((dA×dB)×(dB×(dB×dC))). -/
noncomputable def assoc_equiv (dA dB dC : Type*) :
    BigIdx dA dB dC ≃ MidIdx dA dB dC :=
  Equiv.prodAssoc (dA × dB) dB (dB × dC)
