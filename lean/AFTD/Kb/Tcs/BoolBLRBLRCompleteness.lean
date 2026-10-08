import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRBLRAcceptProb
import AFTD.Kb.Tcs.BoolBLRIsLinearBool
import AFTD.Kb.Tcs.BoolBLRBLRCompletenessAuxHLiftLinear
import AFTD.Kb.Tcs.BoolBLRBLRCompletenessAuxHLinear
import AFTD.Kb.Tcs.BoolFourierExpectation
import AFTD.Kb.Tcs.BoolFourierHypercube

/-!
# BoolBLR.BLR_completeness

Topic: interactive   Node: 17bee95c1b84

Provenance: formalization of a published result. Source: Completeness of the BLR linearity test, as formalized in TCSlib (`BoolBLR.BLR_completeness`). Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Completeness of the BLR linearity test. Let $n$ be a natural number and let $f : \{0,1\}^n \to \{0,1\}$ be linear, meaning that
$f(x \oplus y) = f(x) \oplus f(y)$ for all $x, y \in \{0,1\}^n$. Then the BLR acceptance
probability of $f$ equals $1$; that is, when $x$ and $y$ are drawn uniformly and
independently from $\{0,1\}^n$, the test always accepts.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
/-- Shows that every Boolean linear function passes the BLR test with probability one. **Source:** [OD14, §1.6]. -/
lemma BoolBLR.BLR_completeness {n : ℕ}
    (f : hypercube n → Bool)
    (hlin : is_linear_bool f) :
  BLR_accept_prob f = 1 := by
  -- Restate linearity in convenient form.
  -- Lift to the ±1 world: linearity becomes multiplicativity.
  unfold BLR_accept_prob;
  -- Each indicator becomes 1, and 2^n · 2^n / 2^n / 2^n = 1.
  unfold expectation; norm_num [ (BLR_completeness_aux_h_lift_linear f (BLR_completeness_aux_h_linear f hlin)) ] ;

-- Pr [ BLR accepts f ] ≤ 1 - ε if f is ε-far from any linear function
