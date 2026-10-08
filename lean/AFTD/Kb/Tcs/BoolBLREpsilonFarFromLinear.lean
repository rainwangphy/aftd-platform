import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRBoolDist
import AFTD.Kb.Tcs.BoolBLRIsLinearBool
import AFTD.Kb.Tcs.BoolFourierHypercube

/-!
# BoolBLR.epsilon_far_from_linear

Topic: interactive   Node: 7aa8180a3ef5

Provenance: formalization of a published result. Source: TCSlib, `BoolBLR.epsilon_far_from_linear`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A function $f : \{0,1\}^n \to \{0,1\}$ is \emph{$\varepsilon$-far from linear}
if $0 \le \varepsilon \le 1$ and for every linear function
$g : \{0,1\}^n \to \{0,1\}$ we have $\dist(f, g) \ge \varepsilon$.
-/

open Finset BoolFourier in
/-- Defines when a Boolean function is at least `ε`-far from every linear Boolean function. **Source:** [OD14, §1.6]. -/
def BoolBLR.epsilon_far_from_linear {n : ℕ}
    (f : hypercube n → Bool) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ε ≤ 1 ∧
  ∀ g : hypercube n → Bool,
    is_linear_bool g →
      bool_dist f g ≥ ε

-- f is linear if and only if (-1)^f = χ_S for some S
