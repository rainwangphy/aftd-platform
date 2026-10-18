import AFTD.Prelude
import AFTD.Kb.Tcs.Op258Bounded
import AFTD.Kb.Tcs.Op258HasMonoClique
import AFTD.Kb.Tcs.Op258Forces

/-!
# op_258_forces_two

Topic: combinatorics   Node: 10b980034bd7

Provenance: helper lemma. step towards op_258_triangle_forcing_implies_decay_ramsey

For every decay profile a, a forces a monochromatic K_2.
-/

/-- Sanity witness for the forcing predicate: every profile forces a monochromatic `K_2`, since two adjacent vertices always form one. The content of the target therefore starts at `k = 3`. -/
theorem op_258_forces_two (a : ℕ+ → ℝ) : op_258_forces a 2 := by
  use 2
  intro n hn c hc
  unfold op_258_has_mono_clique
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  let v0 : Fin n := ⟨0, h0⟩
  let v1 : Fin n := ⟨1, h1⟩
  have hne : v0 ≠ v1 := by
    intro h
    have := Fin.mk.inj h
    omega
  have he : s(v0, v1) ∈ (SimpleGraph.completeGraph (Fin n)).edgeSet := by simp [hne]
  let e : (SimpleGraph.completeGraph (Fin n)).edgeSet := ⟨s(v0, v1), he⟩
  use {v0, v1}, c e
  refine ⟨by simp [hne], ?_⟩
  intro u v hu hv huv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · contradiction
  · have h_eq : (⟨s(v0, v1), by simp [huv]⟩ : (SimpleGraph.completeGraph (Fin n)).edgeSet) = e := by
      apply Subtype.ext
      rfl
    rw [h_eq]
  · have h_eq : (⟨s(v1, v0), by simp [huv]⟩ : (SimpleGraph.completeGraph (Fin n)).edgeSet) = e := by
      apply Subtype.ext
      exact Sym2.eq_swap
    rw [h_eq]
  · contradiction
