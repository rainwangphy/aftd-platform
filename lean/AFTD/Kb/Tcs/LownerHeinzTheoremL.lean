import AFTD.Prelude

/-!
# LownerHeinzTheorem.L

Topic: quantum   Node: 9cb292141fb8

Provenance: formalization of a published result. Source: QuantumInfo, `LownerHeinzTheorem.L`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzTheorem.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LownerHeinzTheorem.L
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
open CFC in
abbrev LownerHeinzTheorem.L (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] : Type u :=
  ℋ →L[ℂ] ℋ
