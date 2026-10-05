import AFTD.Prelude

/-!
# fse_leftmost

Topic: mechanism_design   Node: 3de054c8ee6c

The leftmost mechanism: place the facility at the leftmost reported location.
-/

open Finset in
/-- The leftmost mechanism: place the facility at the leftmost reported location. -/
noncomputable def fse_leftmost {n : ℕ} [NeZero n] (x : Fin n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty x
