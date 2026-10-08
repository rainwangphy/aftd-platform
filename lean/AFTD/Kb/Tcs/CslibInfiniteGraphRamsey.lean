import AFTD.Prelude
import AFTD.Kb.Tcs.CslibGoodSelectionsExist
import AFTD.Kb.Tcs.CslibInfinitePigeonholePrinciple

/-!
# Cslib.infinite_graph_ramsey

Topic: combinatorics   Node: 64750b654549

Provenance: formalization of a published result. Source: CSLib, `Cslib.infinite_graph_ramsey`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Combinatorics/InfiniteGraphRamsey.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If the edges of an infinite complete graph is assigned a finite number of colors, then there must exist a color `c` and an infinite set `s` of vertices such that the edge between any two vertices of `s` is assigned the same color `c`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {Vertex Color : Type*} [Finite Color] (color : Finset Vertex → Color) in
variable [Infinite Vertex] in
/-- If the edges of an infinite complete graph is assigned a finite number of colors, then there must exist a color `c` and an infinite set `s` of vertices such that the edge between any two vertices of `s` is assigned the same color `c`. -/
theorem Cslib.infinite_graph_ramsey :
    ∃ c : Color, ∃ s : Set Vertex, s.Infinite ∧
      ∀ e : Finset Vertex, e.card = 2 → ↑e ⊆ s → color e = c := by
  classical
  obtain ⟨vs, v, c, h_sel⟩ := good_selections_exist color
  simp only [forall_and] at h_sel
  obtain ⟨h_vs, h_v, h_c⟩ := h_sel
  have : ∀ m n, m < n → v n ∈ vs m := by
    intro m n h_mn
    suffices h1 : (⋂ m < n, vs m) ⊆ vs m by grind
    exact biInter_subset_of_mem h_mn
  obtain ⟨c', s', h_s'_inf, h_s'_col⟩ :
      ∃ c' : Color, ∃ s' : Set ℕ, s'.Infinite ∧ ∀ n ∈ s', c n = c' := by
    obtain ⟨c', s', h_s'_inf, _, h_s'col⟩ := infinite_pigeonhole_principle c infinite_univ
    use c', s'
  use c', (v '' s')
  have h_v_inj : Injective v := by
    intro _ _
    grind
  split_ands
  · exact Infinite.image (injOn_of_injective h_v_inj (s := s')) h_s'_inf
  · simp only [Finset.card_eq_two]
    grind [Finset.pair_comm, Finset.coe_insert, Finset.coe_singleton]
