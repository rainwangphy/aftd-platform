import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidIsCyclic
import AFTD.Kb.Tcs.SkewZeroForcingClosure
import AFTD.Kb.Tcs.SkewZeroForced

/-!
# matroid_realization_via_circuit_neighborhoods_szf

Topic: graphs   Node: 1f4478daaf85

Provenance: formalization of a published result. Source: arXiv:2611.15741 Proposition 2.10

Let V be a finite type ([Finite V]), let N : V → Set V be a symmetric neighborhood function satisfying u ∈ N v ↔ v ∈ N u for all u, v : V, and let M be a matroid on V with ground set M.E = Set.univ. Suppose that every circuit C of M is the neighborhood of some vertex v : V with N v = C (∀ C, M.IsCircuit C → ∃ v : V, N v = C), and every neighborhood N v is cyclic in M (∀ v : V, Matroid.IsCyclic M (N v)). Then for every subset S : Set V, the skew zero forcing closure equals the matroid closure: skew_zero_forcing_closure N S = M.closure S.
-/

/-- Matroid realization via circuit neighborhoods in skew zero forcing (Proposition 2.10). -/
theorem matroid_realization_via_circuit_neighborhoods_szf {V : Type*} [Finite V] (N : V → Set V) (h_symm : ∀ u v : V, u ∈ N v ↔ v ∈ N u) (M : Matroid V) (hE : M.E = Set.univ) (h_circ : ∀ C, M.IsCircuit C → ∃ v : V, N v = C) (h_cyc : ∀ v : V, Matroid.IsCyclic M (N v)) (S : Set V) : skew_zero_forcing_closure N S = M.closure S := by
  have _ := h_symm
  apply Set.Subset.antisymm
  · rintro w hw
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
  · intro e he
    by_cases heS : e ∈ S
    · exact SkewZeroForced.init e heS
    · rw [Matroid.mem_closure_iff_exists_isCircuit heS] at he
      obtain ⟨C, hCsub, hC, heC⟩ := he
      obtain ⟨v, hv⟩ := h_circ C hC
      rw [← hv] at heC hCsub
      have h_step : SkewZeroForced N S e := by
        apply SkewZeroForced.step v e heC
        intro x hx hxne
        have hxS : x ∈ S := by
          have := hCsub hx
          cases this with
          | inl h => exact False.elim (hxne h)
          | inr h => exact h
        exact SkewZeroForced.init x hxS
      exact h_step
