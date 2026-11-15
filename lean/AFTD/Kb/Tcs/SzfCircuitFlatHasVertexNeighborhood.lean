import AFTD.Prelude
import AFTD.Kb.Tcs.SkewZeroForcingClosure
import AFTD.Kb.Tcs.SkewZeroForced

/-!
# szf_circuit_flat_has_vertex_neighborhood

Topic: graphs   Node: 06f77421f445

Provenance: formalization of a published result. Source: scout/2611-15741-skew-zero-forcing-matroids.md:268

Let M be a matroid on a finite ground set V with M.E = Set.univ. If M is SZF-realized by a graph with symmetric neighborhood function N (u ∈ N v ↔ v ∈ N u), then for every circuit-flat C of M (a subset C ⊆ V that is both a circuit and a flat of M), there exists a vertex v ∈ V such that N v = C.
-/

/-- Every circuit-flat of an SZF-realizable matroid is the neighborhood of some vertex. -/
theorem szf_circuit_flat_has_vertex_neighborhood {V : Type*} [Finite V]
    (M : Matroid V) (hE : M.E = Set.univ)
    (N : V → Set V) (h_symm : ∀ u v, u ∈ N v ↔ v ∈ N u)
    (h_realize : ∀ S : Set V, skew_zero_forcing_closure N S = M.closure S)
    (C : Set V) (hC : M.IsCircuit C ∧ M.IsFlat C) :
    ∃ v : V, N v = C := by
  have _ := h_symm
  have _ := hE
  obtain ⟨e, he⟩ := hC.1.nonempty
  have he_cl : e ∈ M.closure (C \ {e}) := hC.1.mem_closure_sdiff_singleton_of_mem he
  have h_cl_eq : M.closure (C \ {e}) = C := by
    apply Set.Subset.antisymm
    · have h_sub : C \ {e} ⊆ C := Set.sdiff_subset
      have h_le := M.closure_mono h_sub
      rw [hC.2.closure] at h_le
      exact h_le
    · intro x hx
      by_cases hxe : x = e
      · subst hxe
        exact he_cl
      · exact M.mem_closure_of_mem ⟨hx, hxe⟩
  have he_szf : SkewZeroForced N (C \ {e}) e := by
    have h_mem : e ∈ skew_zero_forcing_closure N (C \ {e}) := by
      rw [h_realize, h_cl_eq]
      exact he
    exact h_mem
  have he_not_in : e ∉ C \ {e} := by simp
  cases he_szf with
  | init _ h_in => exact False.elim (he_not_in h_in)
  | step u _ heNu h_all =>
    use u
    have hNu_sub : N u ⊆ C := by
      intro x hx
      by_cases hxe : x = e
      · subst hxe
        exact he
      · have hx_szf : SkewZeroForced N (C \ {e}) x := h_all x hx hxe
        have hx_cl : x ∈ skew_zero_forcing_closure N (C \ {e}) := hx_szf
        rw [h_realize, h_cl_eq] at hx_cl
        exact hx_cl
    apply Set.Subset.antisymm hNu_sub
    by_contra h_not
    have h_ssub : N u ⊂ C := ⟨hNu_sub, h_not⟩
    have h_indep : M.Indep (N u) := hC.1.ssubset_indep h_ssub
    have h_not_cl : e ∉ M.closure (N u \ {e}) := h_indep.notMem_closure_sdiff_of_mem heNu
    have h_szf : SkewZeroForced N (N u \ {e}) e := by
      apply SkewZeroForced.step u e heNu
      intro x hx hxne
      exact SkewZeroForced.init x ⟨hx, hxne⟩
    have h_cl : e ∈ M.closure (N u \ {e}) := by
      have h_mem : e ∈ skew_zero_forcing_closure N (N u \ {e}) := h_szf
      rwa [h_realize] at h_mem
    exact h_not_cl h_cl
