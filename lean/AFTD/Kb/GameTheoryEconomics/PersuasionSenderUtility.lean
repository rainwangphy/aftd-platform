import AFTD.Prelude

/-!
# persuasion_sender_utility

Topic: mechanism_design   Node: 187529b09cf9

Sender utility S(q): expected number of coordinates recommended as 1.
-/

open Finset in
/-- Sender utility `S(q)`: expected number of coordinates recommended as `1`. -/
noncomputable def persuasion_sender_utility {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : (ι → Bool) → (ι → Bool) → ℝ) : ℝ :=
  ∑ x, ∑ a, q x a * ((Finset.univ.filter (fun i => a i = true)).card : ℝ)
