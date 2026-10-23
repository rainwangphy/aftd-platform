import AFTD.Prelude
import AFTD.Kb.Tcs.IsGhzGraph
import AFTD.Kb.Tcs.GhzIsPerfectMatching
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.GhzMatchingIndex
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# ghz_matching_index_le_min_degree

Topic: quantum   Node: 2aabf3734c72

Provenance: formalization of a published result. Source: arXiv:2610.22190 Observation 7

For any finite type V with decidable equality and any connected simple graph G on V with decidable adjacency, the matching index ghz_matching_index G is at most the minimum degree G.minDegree.
-/

open scoped Classical

lemma ghz_matching_index_le_min_degree_ncard_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (c : Sym2 V → ℕ) :
    Set.ncard { vc : V → ℕ |
      (∃ M : Finset (Sym2 V), ghz_is_perfect_matching G M ∧ ∀ e ∈ M, ∀ u : V, u ∈ e → vc u = c e) ∧
      (∃ k : ℕ, ∀ u : V, vc u = k) } ≤ G.degree v := by
  let S := { vc : V → ℕ |
    (∃ M : Finset (Sym2 V), ghz_is_perfect_matching G M ∧ ∀ e ∈ M, ∀ u : V, u ∈ e → vc u = c e) ∧
    (∃ k : ℕ, ∀ u : V, vc u = k) }
  have hinj : Set.InjOn (fun vc => vc v) S := by
    intro vc1 h1 vc2 h2 heq
    change vc1 v = vc2 v at heq
    rcases h1.2 with ⟨k1, hk1⟩
    rcases h2.2 with ⟨k2, hk2⟩
    ext u
    have hu1 : vc1 u = vc1 v := by rw [hk1 u, hk1 v]
    have hu2 : vc2 u = vc2 v := by rw [hk2 u, hk2 v]
    rw [hu1, heq, ← hu2]
  have hcard : S.ncard = ((fun vc => vc v) '' S).ncard := (hinj.ncard_image).symm
  have hsub : (fun vc => vc v) '' S ⊆ (fun u : V => c s(v, u)) '' (G.neighborSet v) := by
    rintro x ⟨vc, hvc, rfl⟩
    dsimp
    rcases hvc.1 with ⟨M, hM, hc⟩
    rcases hM.2 v with ⟨e, ⟨heM, hve⟩, -⟩
    have he_edge : e ∈ G.edgeSet := hM.1 e heM
    have hvc_v : vc v = c e := hc e heM v hve
    induction' e using Sym2.inductionOn with x y
    rw [Sym2.mem_iff] at hve
    rcases hve with rfl | rfl
    · rw [SimpleGraph.mem_edgeSet] at he_edge
      rw [hvc_v]
      exact ⟨y, he_edge, rfl⟩
    · rw [SimpleGraph.mem_edgeSet] at he_edge
      rw [hvc_v]
      refine ⟨x, he_edge.symm, by rw [Sym2.eq_swap]⟩
  have hle1 : ((fun vc => vc v) '' S).ncard ≤ ((fun u : V => c s(v, u)) '' (G.neighborSet v)).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have hle2 : ((fun u : V => c s(v, u)) '' (G.neighborSet v)).ncard ≤ (G.neighborSet v).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  have hdeg : (G.neighborSet v).ncard = G.degree v := by
    have h : (G.neighborSet v).ncard = (G.neighborFinset v : Set V).ncard := by
      congr 1
      exact (G.coe_neighborFinset v).symm
    rw [h, Set.ncard_coe_finset, G.card_neighborFinset_eq_degree]
  show S.ncard ≤ G.degree v
  linarith

lemma ghz_matching_index_le_min_degree_degree_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ghz_matching_index G ≤ G.degree v := by
  let setD := { d : ℕ | ∃ (c : Sym2 V → ℕ) (w : Sym2 V → ℂ), is_ghz_graph G c w ∧
    d = Set.ncard { vc : V → ℕ |
      (∃ M : Finset (Sym2 V), ghz_is_perfect_matching G M ∧ ∀ e ∈ M, ∀ u : V, u ∈ e → vc u = c e) ∧
      (∃ k : ℕ, ∀ u : V, vc u = k) } }
  change sSup setD ≤ G.degree v
  by_cases hne : setD.Nonempty
  · apply csSup_le hne
    rintro d ⟨c, w, hw, rfl⟩
    exact ghz_matching_index_le_min_degree_ncard_le G v c
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, csSup_empty]
    exact Nat.zero_le _

/-- The matching index of a connected simple graph is bounded above by its minimum degree. -/
theorem ghz_matching_index_le_min_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_conn : G.Connected) :
    ghz_matching_index G ≤ G.minDegree := by
  have : Nonempty V := h_conn.nonempty
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  exact ghz_matching_index_le_min_degree_degree_le G v
