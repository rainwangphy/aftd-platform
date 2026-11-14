import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidIsCyclic
import AFTD.Kb.Tcs.SkewZeroForcingClosure
import AFTD.Kb.Tcs.SkewZeroForced

/-!
# skew_zero_forcing_closure_subset_matroid_closure

Topic: graphs   Node: 98935ebae089

Provenance: helper lemma. arXiv:2611.15741 Proposition 2.10

Let V be a finite type ([Finite V]), let N : V → Set V be a symmetric neighborhood function satisfying u ∈ N v ↔ v ∈ N u for all u, v : V, and let M be a matroid on V with ground set M.E = Set.univ. If every neighborhood N v is cyclic in M (∀ v : V, Matroid.IsCyclic M (N v)), then for every subset S : Set V, the skew zero forcing closure is contained in the matroid closure: skew_zero_forcing_closure N S ⊆ M.closure S.
-/

/-- Skew zero forcing closure is contained in matroid closure when every neighborhood is cyclic. -/
theorem skew_zero_forcing_closure_subset_matroid_closure {V : Type*} [Finite V] (N : V → Set V) (h_symm : ∀ u v : V, u ∈ N v ↔ v ∈ N u) (M : Matroid V) (hE : M.E = Set.univ) (h_cyc : ∀ v : V, Matroid.IsCyclic M (N v)) (S : Set V) : skew_zero_forcing_closure N S ⊆ M.closure S := by
  have _ := h_symm
  rintro w (hw : SkewZeroForced N S w)
  induction hw with
  | init v hv =>
    exact M.mem_closure_of_mem hv (by simp [hE])
  | step u w' hw' h_ih ih =>
    obtain ⟨𝒮, hC, hU⟩ := h_cyc u
    have hw'U : w' ∈ ⋃₀ 𝒮 := by rwa [← hU]
    obtain ⟨C, hCin, hw'C⟩ := hw'U
    have hC_circ : M.IsCircuit C := hC C hCin
    have hC_sub : C ⊆ N u := by
      intro x hx
      rw [hU]
      exact Set.mem_sUnion_of_mem hx hCin
    have h_diff_sub : C \ {w'} ⊆ M.closure S := by
      intro x hx
      exact ih x (hC_sub hx.1) hx.2
    have hw'_cl : w' ∈ M.closure (C \ {w'}) :=
      hC_circ.mem_closure_sdiff_singleton_of_mem hw'C
    have h_le := M.closure_mono h_diff_sub
    rw [M.closure_closure S] at h_le
    exact h_le hw'_cl
