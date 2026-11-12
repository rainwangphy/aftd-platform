import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForcingBoundary
import AFTD.Kb.Tcs.ZeroForcingSeq

/-!
# zero_forcing_boundary_mono

Topic: graphs   Node: 2976e0ce29fb

Provenance: formalization of a published result. Source: arXiv:2611.13244, Proposition 2.9 -- Stabilization of the zero forcing number of generalized Petersen graphs

Let G be a simple graph and S a finite subset of vertices. Then for every natural number i, the extended cardinality of the boundary ∂B_{i+1} is at most the extended cardinality of the boundary ∂B_i.
-/

/-- The boundary size is monotonically non-increasing along the zero forcing sequence: |∂B_{i+1}| ≤ |∂B_i| for every i. -/
theorem zero_forcing_boundary_mono {V : Type*} (G : SimpleGraph V) {S : Set V} (hS : S.Finite) (i : ℕ) : (zero_forcing_boundary G (zero_forcing_seq G S (i + 1))).encard ≤ (zero_forcing_boundary G (zero_forcing_seq G S i)).encard := by
  classical
  have _ := hS
  set B := zero_forcing_seq G S i
  set W := {w : V | ∃ x ∈ B, G.neighborSet x \ B = {w}}
  have hB' : zero_forcing_seq G S (i + 1) = B ∪ W := rfl
  have hW : ∀ w ∈ W, ∃ x ∈ B, G.neighborSet x \ B = {w} := fun w hw => hw
  let f : V → V := fun w =>
    if hw : w ∈ W then Classical.choose (hW w hw) else w
  have hf_W : ∀ (w : V) (hw : w ∈ W), f w = Classical.choose (hW w hw) := fun w hw => dif_pos hw
  have hf_not_W : ∀ (w : V) (hw : w ∉ W), f w = w := fun w hw => dif_neg hw

  have h_not_in_boundary : ∀ (w : V) (x : V) (hxB : x ∈ B) (hx : G.neighborSet x \ B = {w}),
      x ∉ zero_forcing_boundary G (B ∪ W) := by
    intro w x hxB hx h
    rw [zero_forcing_boundary] at h
    rcases h with ⟨-, y, hy_adj, hy_notin⟩
    have hy_notin_B : y ∉ B := fun hyB => hy_notin (Set.mem_union_left _ hyB)
    have hy_diff : y ∈ G.neighborSet x \ B := ⟨hy_adj, hy_notin_B⟩
    rw [hx, Set.mem_singleton_iff] at hy_diff
    subst hy_diff
    exact hy_notin (Set.mem_union_right _ ⟨x, hxB, hx⟩)

  have h_in_boundary_of_W : ∀ (w : V) (x : V) (hxB : x ∈ B) (hx : G.neighborSet x \ B = {w}),
      x ∈ zero_forcing_boundary G B := by
    intro w x hxB hx
    rw [zero_forcing_boundary]
    refine ⟨hxB, w, ?_, ?_⟩
    · have hw : w ∈ G.neighborSet x \ B := by rw [hx]; exact Set.mem_singleton w
      exact hw.1
    · have hw : w ∈ G.neighborSet x \ B := by rw [hx]; exact Set.mem_singleton w
      exact hw.2

  have h_in_boundary_of_not_W : ∀ (v : V),
      v ∈ zero_forcing_boundary G (B ∪ W) → v ∉ W → v ∈ zero_forcing_boundary G B := by
    intro v hv hvnw
    rw [zero_forcing_boundary] at hv ⊢
    rcases hv with ⟨hvBW, y, hy_adj, hy_notin⟩
    have hvB : v ∈ B := by
      cases hvBW with
      | inl h => exact h
      | inr h => exact False.elim (hvnw h)
    refine ⟨hvB, y, hy_adj, fun hyB => hy_notin (Set.mem_union_left _ hyB)⟩

  have h_maps : Set.MapsTo f (zero_forcing_boundary G (B ∪ W)) (zero_forcing_boundary G B) := by
    intro v hv
    by_cases hw : v ∈ W
    · rw [hf_W v hw]
      have hspec := Classical.choose_spec (hW v hw)
      exact h_in_boundary_of_W v (Classical.choose (hW v hw)) hspec.1 hspec.2
    · rw [hf_not_W v hw]
      exact h_in_boundary_of_not_W v hv hw

  have h_inj : Set.InjOn f (zero_forcing_boundary G (B ∪ W)) := by
    intro u hu v hv heq
    by_cases huW : u ∈ W <;> by_cases hvW : v ∈ W
    · rw [hf_W u huW, hf_W v hvW] at heq
      have hu_spec := Classical.choose_spec (hW u huW)
      have hv_spec := Classical.choose_spec (hW v hvW)
      have h_eq_sets : ({u} : Set V) = {v} := by
        rw [← hu_spec.2, heq, hv_spec.2]
      exact Set.singleton_eq_singleton_iff.mp h_eq_sets
    · rw [hf_W u huW, hf_not_W v hvW] at heq
      have hu_spec := Classical.choose_spec (hW u huW)
      have h_u_notin := h_not_in_boundary u (Classical.choose (hW u huW)) hu_spec.1 hu_spec.2
      rw [heq] at h_u_notin
      exact False.elim (h_u_notin hv)
    · rw [hf_not_W u huW, hf_W v hvW] at heq
      have hv_spec := Classical.choose_spec (hW v hvW)
      have h_v_notin := h_not_in_boundary v (Classical.choose (hW v hvW)) hv_spec.1 hv_spec.2
      rw [← heq] at h_v_notin
      exact False.elim (h_v_notin hu)
    · rw [hf_not_W u huW, hf_not_W v hvW] at heq
      exact heq

  rw [hB']
  exact Set.encard_le_encard_of_injOn h_maps h_inj
