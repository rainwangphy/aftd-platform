import AFTD.Prelude
import AFTD.Kb.Tcs.AnticompleteVertexFourDisjointNonneighborSetsBound

/-!
# boundary_five_blocks_vertex_nonneighbor_defects

Topic: graphs   Node: 983c9af657b7

Provenance: helper lemma. OP-1957: graph-to-count transfer for the size-five block forced-edge route (IN-1126).

In the four-block boundary graph on 4k vertices with blocks A and C of size five, A anticomplete to B, C anticomplete to D and minimum degree at least 2k+2, four pairwise disjoint sets of non-neighbors of a vertex v have at most 2 vertices outside B in total if v is in A, at most 2k-8 outside A if v is in B, at most 2 outside D if v is in C, and at most 2k-8 outside C if v is in D.
-/

theorem boundary_five_blocks_vertex_nonneighbor_defects
    (k : ℕ) (hk : 5 ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hA : A.card=5) (hC : C.card=5)
    (hsizeAB : A.card+B.card=2*k) (hsizeCD : C.card+D.card=2*k)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (v : Fin (4*k)) (s1 s2 s3 s4 : Finset (Fin (4*k)))
    (hs : ∀ w, (w ∈ s1 ∨ w ∈ s2 ∨ w ∈ s3 ∨ w ∈ s4) → w ≠ v ∧ ¬ G.Adj v w)
    (d12 : Disjoint s1 s2) (d13 : Disjoint s1 s3) (d14 : Disjoint s1 s4)
    (d23 : Disjoint s2 s3) (d24 : Disjoint s2 s4) (d34 : Disjoint s3 s4) :
    (v ∈ A → (s1 \ B).card + (s2 \ B).card + (s3 \ B).card + (s4 \ B).card ≤ 2) ∧
    (v ∈ B → (s1 \ A).card + (s2 \ A).card + (s3 \ A).card + (s4 \ A).card + 8 ≤ 2*k) ∧
    (v ∈ C → (s1 \ D).card + (s2 \ D).card + (s3 \ D).card + (s4 \ D).card ≤ 2) ∧
    (v ∈ D → (s1 \ C).card + (s2 \ C).card + (s3 \ C).card + (s4 \ C).card + 8 ≤ 2*k) := by
  have hcard : Fintype.card (Fin (4*k)) = 4*k := Fintype.card_fin _
  have hdv := hdegree v
  refine ⟨fun hv => ?_, fun hv => ?_, fun hv => ?_, fun hv => ?_⟩
  · exact anticomplete_vertex_four_disjoint_nonneighbor_sets_bound G B v (Finset.disjoint_left.mp hAB hv) (hnoAB v hv) (2*k+4) 2
      (by omega) (by omega) s1 s2 s3 s4 hs d12 d13 d14 d23 d24 d34
  · have := anticomplete_vertex_four_disjoint_nonneighbor_sets_bound G A v (Finset.disjoint_right.mp hAB hv)
      (fun a ha h => hnoAB a ha v hv h.symm) (4*k-6) (2*k-8)
      (by omega) (by omega) s1 s2 s3 s4 hs d12 d13 d14 d23 d24 d34
    omega
  · exact anticomplete_vertex_four_disjoint_nonneighbor_sets_bound G D v (Finset.disjoint_left.mp hCD hv) (hnoCD v hv) (2*k+4) 2
      (by omega) (by omega) s1 s2 s3 s4 hs d12 d13 d14 d23 d24 d34
  · have := anticomplete_vertex_four_disjoint_nonneighbor_sets_bound G C v (Finset.disjoint_right.mp hCD hv)
      (fun a ha h => hnoCD a ha v hv h.symm) (4*k-6) (2*k-8)
      (by omega) (by omega) s1 s2 s3 s4 hs d12 d13 d14 d23 d24 d34
    omega
