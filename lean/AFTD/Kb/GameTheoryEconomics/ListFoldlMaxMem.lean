import AFTD.Prelude

/-!
# List.foldl_max_mem

Topic: equilibria   Node: 1f239e6b37d5

Provenance: formalization of a published result. Source: EconCSLib, `List.foldl_max_mem`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Argmax.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`foldl_max_mem`: the running maximizer kept by the left fold lies in the candidate list `acc :: l`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {X Y : Type*} in
/-- `foldl_max_mem`: the running maximizer kept by the left fold lies in the candidate list `acc :: l`. -/
theorem List.foldl_max_mem [LE Y] [DecidableLE Y] (f : X → Y) :
    ∀ (l : List X) (acc : X),
      l.foldl (fun a z => if f a ≤ f z then z else a) acc ∈ acc :: l := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons y ys ih =>
      intro acc
      rw [List.foldl_cons]
      by_cases h : f acc ≤ f y
      · rw [if_pos h]
        exact List.mem_cons_of_mem acc (ih y)
      · rw [if_neg h]
        rcases List.mem_cons.mp (ih acc) with hr | hr
        · rw [hr]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem acc (List.mem_cons_of_mem y hr)
