import AFTD.Prelude

/-!
# Bra

Topic: quantum   Node: cea20f4e470b

Provenance: formalization of a published result. Source: QuantumInfo, `Bra`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A bra is identical in definition to a `Ket`, but are separate to avoid complex conjugation confusion. They can be interconverted with the adjoint: `Ket.to_bra` and `Bra.to_ket`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open BigOperators in
open ComplexConjugate in
open Kronecker in
open scoped Matrix ComplexOrder in
variable (d : Type*) [Fintype d] in
/-- A bra is identical in definition to a `Ket`, but are separate to avoid complex conjugation confusion. They can be interconverted with the adjoint: `Ket.to_bra` and `Bra.to_ket` -/
structure Bra where
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖ ^ 2 =1
