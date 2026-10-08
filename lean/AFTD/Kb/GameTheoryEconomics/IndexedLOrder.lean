import AFTD.Prelude

/-!
# IndexedLOrder

Topic: general_equilibrium   Node: 42043a1be943

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A family of linear orders on `T` indexed by `I`. Each `i : I` provides a linear order `IST i : LinearOrder T` on the type `T`. This is the abstract setting for Scarf's lemma: the index set `I` plays the role of coordinate directions, and the orders encode how each direction ranks the points of `T`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
variable {T : Type*} [Inhabited T] in
variable {I : Type*} in
/-- A family of linear orders on `T` indexed by `I`. Each `i : I` provides a linear order `IST i : LinearOrder T` on the type `T`. This is the abstract setting for Scarf's lemma: the index set `I` plays the role of coordinate directions, and the orders encode how each direction ranks the points of `T`. -/
class IndexedLOrder (I T :Type*) where
  IST : I → LinearOrder T
