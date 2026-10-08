import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRBLRAcceptProb
import AFTD.Kb.Tcs.BoolBLRLiftPm1
import AFTD.Kb.Tcs.BoolBLRBLRAcceptProbPm1AuxHEq
import AFTD.Kb.Tcs.BoolFourierCardHypercube
import AFTD.Kb.Tcs.BoolFourierExpectation
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierXorVec

/-!
# BoolBLR.BLR_accept_prob_pm1

Topic: interactive   Node: c64a3d328681

Provenance: helper lemma. TCSlib, `BoolBLR.BLR_accept_prob_pm1`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BLR acceptance probability in ±1 form. Let $f : \{0,1\}^n \to \{0,1\}$ be a Boolean-valued function, and write $F(x) =
(-1)^{f(x)} \in \{\pm 1\}$ for its sign lift. Then the BLR acceptance probability of
$f$, the probability that $F(x \oplus y) = F(x)\,F(y)$ when $x$ and $y$ are drawn
independently and uniformly from $\{0,1\}^n$, satisfies
\[
  \Pr_{x,y}[\text{BLR accepts}]
  \;=\;
  \frac{1 + \E_{x}\!\left[\E_{y}\!\left[ F(x)\,F(y)\,F(x \oplus y) \right]\right]}{2},
\]
where $x \oplus y$ denotes the componentwise XOR.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
/-- Expresses BLR acceptance probability through the `{±1}` triple correlation. **Source:** [OD14, §1.6]. -/
lemma BoolBLR.BLR_accept_prob_pm1 {n : ℕ} (f : hypercube n → Bool) :
  BLR_accept_prob f
  = (1 + expectation (fun x =>
        expectation (fun y =>
          lift_pm1 f x * lift_pm1 f y * lift_pm1 f (xor_vec x y)))) / 2 := by
  unfold BLR_accept_prob expectation;
  -- Pointwise, the indicator equals (1 + product of three ±1 values)/2.
  -- Push the (1 + …)/2 form through expectations.
  simp_all +decide [ Finset.sum_add_distrib, add_div , (BLR_accept_prob_pm1_aux_h_eq f)];
  norm_num [ ← Finset.sum_div _ _ _, card_hypercube ] ; ring

-- E [ E [ f(x) f(y) f(x + y) ] ] = E [ f(x) E [ f(y) f(x + y) ] ] = E [ f(x) (f * f) (x) ]
