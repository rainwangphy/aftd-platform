import AFTD.Prelude
import AFTD.Kb.Tcs.SzfCircuitFlatHasVertexNeighborhood
import AFTD.Kb.Tcs.SkewZeroForcingClosure

/-!
# not_szf_realizable_of_lt_circuit_flat_card

Topic: graphs   Node: af09a1bef748

Provenance: formalization of a published result. Source: scout/2611-15741-skew-zero-forcing-matroids.md:277

Let M be a finite matroid on ground set V with M.E = Set.univ. If the number of circuit-flats of M strictly exceeds the number of elements in M, then M is not SZF-realizable by any graph with symmetric neighborhood function.
-/

/-- A finite matroid whose number of circuit-flats exceeds its ground set cardinality is not SZF-realizable. -/
theorem not_szf_realizable_of_lt_circuit_flat_card {V : Type*} [Fintype V]
    (M : Matroid V) (hE : M.E = Set.univ)
    (h : Fintype.card V < {C : Set V | M.IsCircuit C ∧ M.IsFlat C}.ncard) :
    ¬ ∃ (N : V → Set V) (_ : ∀ u v, u ∈ N v ↔ v ∈ N u),
      ∀ S : Set V, skew_zero_forcing_closure N S = M.closure S := by
  rintro ⟨N, h_symm, h_realize⟩
  have hsub : {C : Set V | M.IsCircuit C ∧ M.IsFlat C} ⊆ Set.range N := by
    rintro C hC
    obtain ⟨v, hv⟩ := szf_circuit_flat_has_vertex_neighborhood M hE N h_symm h_realize C hC
    exact ⟨v, hv⟩
  have hfin : (Set.range N).Finite := Set.finite_range N
  have hle1 : {C : Set V | M.IsCircuit C ∧ M.IsFlat C}.ncard ≤ (Set.range N).ncard :=
    Set.ncard_le_ncard hsub hfin
  have hle2 : (Set.range N).ncard ≤ Fintype.card V := by
    rw [← Set.image_univ]
    have hle := Set.ncard_image_le (s := Set.univ) (f := N)
    have huni : (Set.univ : Set V).ncard = Fintype.card V := by simp
    omega
  omega
