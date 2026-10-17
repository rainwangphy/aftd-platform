import AFTD.Prelude

/-!
# Ket

Topic: quantum   Node: 60145d2edb1b

Provenance: formalization of a published result. Source: QuantumInfo, `Ket`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A ket as a vector of unit norm. We follow the convention in `Matrix` of vectors as simple functions from a Fintype. Kets are distinctly not a vector space in our notion, as they represent only normalized states and so cannot (in general) be added or scaled.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open BigOperators in
open ComplexConjugate in
open Kronecker in
open scoped Matrix ComplexOrder in
variable (d : Type*) [Fintype d] in
/-- A ket as a vector of unit norm. We follow the convention in `Matrix` of vectors as simple functions from a Fintype. Kets are distinctly not a vector space in our notion, as they represent only normalized states and so cannot (in general) be added or scaled. -/
structure Ket where
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖ ^ 2 = 1
  --TODO: change to `vec : EuclideanSpace ℂ d` / `normalized' : ‖vec‖ = 1`
