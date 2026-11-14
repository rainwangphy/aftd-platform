import AFTD.Prelude
import AFTD.Kb.Tcs.SkewZeroForcingClosure
import AFTD.Kb.Tcs.SkewZeroForced

/-!
# matroid_closure_subset_skew_zero_forcing_closure

Topic: graphs   Node: fbdd608d4cd2

Provenance: helper lemma. arXiv:2611.15741 Proposition 2.10

Let V be a finite type ([Finite V]), let N : V → Set V be a symmetric neighborhood function satisfying u ∈ N v ↔ v ∈ N u for all u, v : V, and let M be a matroid on V with ground set M.E = Set.univ. If every circuit C of M is the neighborhood of some vertex v : V with N v = C (∀ C, M.IsCircuit C → ∃ v : V, N v = C), then for every subset S : Set V, the matroid closure is contained in the skew zero forcing closure: M.closure S ⊆ skew_zero_forcing_closure N S.
-/

/-- Matroid closure is contained in skew zero forcing closure when every circuit is a neighborhood. -/
theorem matroid_closure_subset_skew_zero_forcing_closure {V : Type*} [Finite V] (N : V → Set V) (h_symm : ∀ u v : V, u ∈ N v ↔ v ∈ N u) (M : Matroid V) (hE : M.E = Set.univ) (h_circ : ∀ C, M.IsCircuit C → ∃ v : V, N v = C) (S : Set V) : M.closure S ⊆ skew_zero_forcing_closure N S := by
  have _ := h_symm
  have _ := hE
  intro e he
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
