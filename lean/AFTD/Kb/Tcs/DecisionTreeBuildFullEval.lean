import AFTD.Prelude
import AFTD.Kb.Tcs.DecisionTreeBuildFull
import AFTD.Kb.Tcs.DecisionTreeEval
import AFTD.Kb.Tcs.DecisionTree

/-!
# DecisionTree.buildFull_eval

Topic: combinatorics   Node: 5f96f708a447

Provenance: helper lemma. TCSlib, `DecisionTree.buildFull_eval`. Lean proof by Hydroxyi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/DecisionTree.lean (Copyright (c) 2026 TCSlib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The complete tree computes `f` on every input it is consistent with. **Proof sketch.** Induction on the number of variables still to be queried, following the recursion that builds the tree. The invariant carried along is that the accumulator already agrees with the input on the coordinates queried so far. If variables remain, the tree branches on the next coordinate and evaluation follows the branch named by the input's value there; updating the accumulator at that coordinate to that same value extends the agreement by one coordinate, which is exactly the hypothesis the induction step needs. If none remain, the tree is the leaf holding `f` of the accumulator, and the invariant now covers every coordinate, so the accumulator and the input are equal as functions and the leaf is `f` of the input.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The complete tree computes `f` on every input it is consistent with. **Proof sketch.** Induction on the number of variables still to be queried, following the recursion that builds the tree. The invariant carried along is that the accumulator already agrees with the input on the coordinates queried so far. If variables remain, the tree branches on the next coordinate and evaluation follows the branch named by the input's value there; updating the accumulator at that coordinate to that same value extends the agreement by one coordinate, which is exactly the hypothesis the induction step needs. If none remain, the tree is the leaf holding `f` of the accumulator, and the invariant now covers every coordinate, so the accumulator and the input are equal as functions and the leaf is `f` of the input. -/
lemma DecisionTree.buildFull_eval {n : ℕ} (f : (Fin n → Bool) → Bool)
    (k : ℕ) (hk : k ≤ n) (acc x : Fin n → Bool)
    (hinv : ∀ i : Fin n, i.val < k → acc i = x i) :
    (DecisionTree.buildFull f k acc).eval x = f x := by
  unfold DecisionTree.buildFull
  split
  · rename_i h
    simp only [DecisionTree.eval]
    cases hxv : x ⟨k, h⟩ with
    | false =>
      rw [if_neg (by decide : ¬(false = true))]
      apply DecisionTree.buildFull_eval f (k + 1) (by omega)
      intro i hi
      by_cases heq : i = ⟨k, h⟩
      · subst heq; simp [Function.update, hxv]
      · simp only [Function.update, heq]
        exact hinv i (by have : i.val ≠ k := fun hv => heq (Fin.ext hv); omega)
    | true =>
      rw [if_pos rfl]
      apply DecisionTree.buildFull_eval f (k + 1) (by omega)
      intro i hi
      by_cases heq : i = ⟨k, h⟩
      · subst heq; simp [Function.update, hxv]
      · simp only [Function.update, heq]
        exact hinv i (by have : i.val ≠ k := fun hv => heq (Fin.ext hv); omega)
  · simp only [DecisionTree.eval]
    have : acc = x := funext fun i => hinv i (by omega)
    rw [this]
termination_by n - k
