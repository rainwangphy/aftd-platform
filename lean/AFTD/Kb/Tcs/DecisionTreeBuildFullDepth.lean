import AFTD.Prelude
import AFTD.Kb.Tcs.DecisionTreeBuildFull
import AFTD.Kb.Tcs.DecisionTreeDepth

/-!
# DecisionTree.buildFull_depth

Topic: combinatorics   Node: bb04591a434a

Provenance: helper lemma. TCSlib, `DecisionTree.buildFull_depth`. Lean proof by Hydroxyi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/DecisionTree.lean (Copyright (c) 2026 TCSlib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The complete tree started at level `k` has depth at most `n - k`.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The complete tree started at level `k` has depth at most `n - k`. -/
lemma DecisionTree.buildFull_depth {n : ℕ} (f : (Fin n → Bool) → Bool)
    (k : ℕ) (_ : k ≤ n) (acc : Fin n → Bool) :
    (DecisionTree.buildFull f k acc).depth ≤ n - k := by
  unfold DecisionTree.buildFull
  split
  · rename_i h
    simp only [DecisionTree.depth]
    have h1 := DecisionTree.buildFull_depth f (k + 1) (by omega)
      (Function.update acc ⟨k, h⟩ false)
    have h2 := DecisionTree.buildFull_depth f (k + 1) (by omega)
      (Function.update acc ⟨k, h⟩ true)
    have h3 := max_le h1 h2
    omega
  · simp [DecisionTree.depth]
termination_by n - k
