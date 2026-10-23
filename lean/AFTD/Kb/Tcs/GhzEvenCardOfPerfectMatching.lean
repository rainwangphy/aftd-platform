import AFTD.Prelude
import AFTD.Kb.Tcs.GhzIsPerfectMatching

/-!
# ghz_even_card_of_perfect_matching

Topic: quantum   Node: 173f30dd4b43

Provenance: helper lemma. arXiv:2610.22190 Section 2

For any finite type V and any simple graph G on V, if M is a perfect matching of G (ghz_is_perfect_matching G M), then the cardinality of V is even.
-/

/-- A finite simple graph with a perfect matching has an even number of vertices. -/
lemma ghz_even_card_of_perfect_matching {V : Type*} [Fintype V]
    (G : SimpleGraph V) (M : Finset (Sym2 V)) (hM : ghz_is_perfect_matching G M) :
    Even (Fintype.card V) := by
  classical
  rw [ghz_is_perfect_matching] at hM
  obtain ⟨hmem, hcov⟩ := hM
  -- every vertex lies in at most one matching edge (uniqueness form)
  have huniq : ∀ v (e e' : Sym2 V), e ∈ M → v ∈ e → e' ∈ M → v ∈ e' → e = e' := by
    intro v e e' he hv he' hv'
    obtain ⟨e0, _he0, hu⟩ := hcov v
    exact (hu e ⟨he, hv⟩).trans (hu e' ⟨he', hv'⟩).symm
  -- the vertices are the disjoint union of the vertex sets of the matching edges
  have hunion : Finset.univ = M.biUnion (fun e => e.toFinset) := by
    ext v
    simp only [Finset.mem_univ, Finset.mem_biUnion, Sym2.mem_toFinset]
    constructor
    · intro _
      obtain ⟨e, he, _⟩ := hcov v
      exact ⟨e, he.1, he.2⟩
    · intro _
      trivial
  have hdisj : (M : Set (Sym2 V)).PairwiseDisjoint (fun e => e.toFinset) := by
    intro e he e' he' hne
    show Disjoint e.toFinset e'.toFinset
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact hne (huniq v e e' he (Sym2.mem_toFinset.mp hv) he' (Sym2.mem_toFinset.mp hv'))
  have hcard : Fintype.card V = ∑ e ∈ M, e.toFinset.card := by
    rw [← Finset.card_univ, hunion, Finset.card_biUnion hdisj]
  -- each matching edge has exactly two endpoints, since it lies in the edge set (no loops)
  have htwo : ∀ e ∈ M, e.toFinset.card = 2 := by
    intro e he
    exact Sym2.card_toFinset_of_not_isDiag e (SimpleGraph.not_isDiag_of_mem_edgeSet G (hmem e he))
  rw [hcard, Finset.sum_const_nat htwo]
  exact ⟨M.card, by ring⟩
