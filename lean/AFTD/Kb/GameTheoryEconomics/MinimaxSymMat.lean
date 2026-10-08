import AFTD.Prelude

/-!
# Minimax.symMat

Topic: equilibria   Node: 5ad7a001f879

Provenance: formalization of a published result. Source: EconCSLib, `Minimax.symMat`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Minimax.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The skew-symmetric symmetrisation of a game `A` on `I ⊕ J ⊕ Unit`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Nonempty I] [Nonempty J] in
/-- The skew-symmetric symmetrisation of a game `A` on `I ⊕ J ⊕ Unit`. -/
def Minimax.symMat (A : I → J → 𝕜) : (I ⊕ J ⊕ Unit) → (I ⊕ J ⊕ Unit) → 𝕜
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inl i, Sum.inr (Sum.inl j) => A i j
  | Sum.inl _, Sum.inr (Sum.inr _) => -1
  | Sum.inr (Sum.inl j), Sum.inl i => -A i j
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => 1
  | Sum.inr (Sum.inr _), Sum.inl _ => 1
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => -1
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => 0
