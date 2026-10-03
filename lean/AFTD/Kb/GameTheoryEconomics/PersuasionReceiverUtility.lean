import AFTD.Prelude

/-!
# persuasion_receiver_utility

Topic: mechanism_design   Node: 14286abb01d8

Receiver utility R(q): expected number of correctly guessed coordinates.
-/

open Finset in
/-- Receiver utility `R(q)`: expected number of correctly guessed coordinates. -/
noncomputable def persuasion_receiver_utility {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : (ι → Bool) → (ι → Bool) → ℝ) : ℝ :=
  ∑ x, ∑ a, q x a * ((Finset.univ.filter (fun i => a i = x i)).card : ℝ)
