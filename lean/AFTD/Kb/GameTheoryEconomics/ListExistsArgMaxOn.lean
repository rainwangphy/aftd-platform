import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# List.exists_argMax_on

Topic: equilibria   Node: 8938d1fd7320

Provenance: formalization of a published result. Source: EconCSLib, `List.exists_argMax_on`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Argmax.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Existence of an argmax** on a non-empty list under a total preorder. Since the preorder may lack antisymmetry, ties are allowed — we only claim existence of *some* maximizer, not uniqueness.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {X Y : Type*} in
/-- **Existence of an argmax** on a non-empty list under a total preorder. Since the preorder may lack antisymmetry, ties are allowed — we only claim existence of *some* maximizer, not uniqueness. -/
theorem List.exists_argMax_on [TotalPreorder Y] (f : X → Y)
    (head : X) (tail : List X) :
    ∃ m, m ∈ head :: tail ∧ ∀ x ∈ head :: tail, f x ≤ f m := by
  induction tail generalizing head with
  | nil =>
      refine ⟨head, List.mem_singleton.mpr rfl, ?_⟩
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact le_refl _
  | cons y ys ih =>
      obtain ⟨m', hm'_mem, hm'_max⟩ := ih y
      rcases TotalPreorder.le_total (f m') (f head) with hle | hle
      · refine ⟨head, List.mem_cons_self, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx_in
        · exact le_refl _
        · exact le_trans (hm'_max x hx_in) hle
      · refine ⟨m', ?_, ?_⟩
        · exact List.mem_cons.mpr (Or.inr hm'_mem)
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx_in
          · exact hle
          · exact hm'_max x hx_in
