import AFTD.Prelude

/-!
# LownerHeinzCore.cfcR

Topic: quantum   Node: e8c80c27252b

Provenance: formalization of a published result. Source: QuantumInfo, `LownerHeinzCore.cfcR`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzCore.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LownerHeinzCore.cfcR
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
open CFC in
variable {𝓐 : Type u} in
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] in
variable [Nontrivial 𝓐] in
noncomputable abbrev LownerHeinzCore.cfcR (f : ℝ → ℝ) (A : 𝓐) : 𝓐 :=
  cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) f A
