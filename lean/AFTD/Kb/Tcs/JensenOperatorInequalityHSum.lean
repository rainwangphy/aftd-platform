import AFTD.Prelude

/-!
# JensenOperatorInequality.HSum

Topic: quantum   Node: 48478c0242dd

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.HSum`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/BlockDiagonal.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A two-fold Hilbert sum used for the block-operator proof of Jensen's inequality. The inner-product instance on `ℋ` is unused by the underlying type synonym but kept to document that `HSum ℋ` is the `ℓ²` direct sum of two copies of a Hilbert space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
/-- A two-fold Hilbert sum used for the block-operator proof of Jensen's inequality. The inner-product instance on `ℋ` is unused by the underlying type synonym but kept to document that `HSum ℋ` is the `ℓ²` direct sum of two copies of a Hilbert space. -/
@[nolint unusedArguments]
abbrev JensenOperatorInequality.HSum (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] : Type u :=
  PiLp 2 (fun _ : Fin 2 => ℋ)
