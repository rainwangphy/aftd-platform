import AFTD.Prelude
import AFTD.Kb.Tcs.DecisionTree

/-!
# DecisionTree.buildFull

Topic: combinatorics   Node: 018fc0cbc907

Provenance: formalization of a published result. Source: TCSlib, `DecisionTree.buildFull`. Lean proof by Hydroxyi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/DecisionTree.lean (Copyright (c) 2026 TCSlib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Build a complete decision tree querying variables 0, 1, …, n−1 in order.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Build a complete decision tree querying variables 0, 1, …, n−1 in order. -/
def DecisionTree.buildFull {n : ℕ} (f : (Fin n → Bool) → Bool)
    (k : ℕ) (acc : Fin n → Bool) : DecisionTree n :=
  if h : k < n then
    .branch ⟨k, h⟩
      (DecisionTree.buildFull f (k + 1) (Function.update acc ⟨k, h⟩ false))
      (DecisionTree.buildFull f (k + 1) (Function.update acc ⟨k, h⟩ true))
  else
    .leaf (f acc)
termination_by n - k
