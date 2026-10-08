import AFTD.Prelude

/-!
# LossSeq

Topic: learning   Node: e9b44434d97d

Provenance: formalization of a published result. Source: TCSlib, `LossSeq`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A \emph{loss sequence} $\ell$ for $N$ experts over $T$ rounds is a function
$\ell : \mathrm{Fin}\,T \to \mathrm{Fin}\,N \to \mathbb{R}$, i.e., at each round
$t < T$ the adversary reveals a loss vector $\ell_t : \mathrm{Fin}\,N \to \mathbb{R}$
whose values are intended to lie in $[0,1]$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The type of loss sequences over `N` experts and `T` rounds: a whole `T × N` trajectory, `ℓ t i` being the loss of expert `i` at round `t` [CBL06, §2.1]. The `[0, 1]` range condition is kept as a separate predicate (`LossSeq.Valid`) instead of being built into the type, which keeps the algebraic definitions simple. -/
def LossSeq (N T : ℕ) := Fin T → Fin N → ℝ
