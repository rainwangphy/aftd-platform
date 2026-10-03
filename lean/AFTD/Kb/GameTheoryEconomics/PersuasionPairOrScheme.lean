import AFTD.Prelude

/-!
# persuasion_pair_or_scheme

Topic: mechanism_design   Node: 3abe663cde2b

The pair-OR scheme of a symmetric coupling ν: draw (X, Y) ∼ ν and recommend X ∨ Y.
-/

open Finset in
/-- The pair-OR scheme of a symmetric coupling `ν`: draw `(X, Y) ∼ ν` and recommend `X ∨ Y`. -/
noncomputable def persuasion_pair_or_scheme {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : (ι → Bool) → (ι → Bool) → ℝ) : (ι → Bool) → (ι → Bool) → ℝ :=
  fun x a => ∑ y, if (fun i => x i || y i) = a then ν x y else 0
