import AFTD.Prelude

/-!
# decay_ramsey_arrow_mono

Topic: combinatorics   Node: ecf09de33964

Provenance: helper lemma. arXiv:2610.20577, Section 1

For every sequence a : ℕ+ → ℝ and integer k ≥ 2, if every a-bounded colouring of sufficiently large complete graphs contains a monochromatic K_{k+1}, then every a-bounded colouring contains a monochromatic K_k.
-/

/-- Monotonicity of the arrow relation: forcing K_{k+1} implies forcing K_k. -/
theorem decay_ramsey_arrow_mono (a : ℕ+ → ℝ) (k : ℕ) (hk : 2 ≤ k)
    (h : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+,
      (∀ i : ℕ+, ((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter (fun e => c e = i)).card ≤ a i * (n.choose 2 : ℝ)) →
      ∃ (s : Finset (Fin n)) (i : ℕ+), s.card = k + 1 ∧
        ∀ ⦃u v : Fin n⦄, u ∈ s → v ∈ s → (h : u ≠ v) →
          c ⟨s(u, v), by simp [SimpleGraph.completeGraph_eq_top, h]⟩ = i) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+,
      (∀ i : ℕ+, ((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter (fun e => c e = i)).card ≤ a i * (n.choose 2 : ℝ)) →
      ∃ (s : Finset (Fin n)) (i : ℕ+), s.card = k ∧
        ∀ ⦃u v : Fin n⦄, u ∈ s → v ∈ s → (h : u ≠ v) →
          c ⟨s(u, v), by simp [SimpleGraph.completeGraph_eq_top, h]⟩ = i := by
  obtain ⟨n₀, hn₀⟩ := h
  refine ⟨n₀, fun n hn c hc => ?_⟩
  obtain ⟨s, i, hcard, hcol⟩ := hn₀ n hn c hc
  have hk_le : k ≤ s.card := by omega
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hk_le
  exact ⟨t, i, htcard, fun u v hut hvt huv => hcol (hts hut) (hts hvt) huv⟩
