import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# List.foldl_max_ge

Topic: equilibria   Node: ec16135ea4b1

Provenance: formalization of a published result. Source: EconCSLib, `List.foldl_max_ge`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Argmax.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`foldl_max_ge`: every element's `f`-image is `≤` that of the running maximizer kept by the left fold. The induction generalizes the accumulator.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {X Y : Type*} in
/-- `foldl_max_ge`: every element's `f`-image is `≤` that of the running maximizer kept by the left fold. The induction generalizes the accumulator. -/
theorem List.foldl_max_ge [TotalPreorder Y] [DecidableLE Y] (f : X → Y) :
    ∀ (l : List X) (acc : X), ∀ x ∈ acc :: l,
      f x ≤ f (l.foldl (fun a z => if f a ≤ f z then z else a) acc) := by
  intro l
  induction l with
  | nil =>
      intro acc x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact le_refl _
  | cons y ys ih =>
      intro acc x hx
      rw [List.foldl_cons]
      by_cases h : f acc ≤ f y
      · rw [if_pos h]
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact le_trans h (ih y y List.mem_cons_self)
        · exact ih y x hx'
      · rw [if_neg h]
        have hy : f y ≤ f acc := by
          rcases TotalPreorder.le_total (f y) (f acc) with hle | hle
          · exact hle
          · exact absurd hle h
        rcases List.mem_cons.mp hx with heq | hx'
        · rw [heq]; exact ih acc acc List.mem_cons_self
        · rcases List.mem_cons.mp hx' with rfl | hx''
          · exact le_trans hy (ih acc acc List.mem_cons_self)
          · exact ih acc x (List.mem_cons.mpr (Or.inr hx''))
