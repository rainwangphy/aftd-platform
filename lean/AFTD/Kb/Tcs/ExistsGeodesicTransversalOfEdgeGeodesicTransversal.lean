import AFTD.Prelude
import AFTD.Kb.Tcs.IsGeodesicTransversal
import AFTD.Kb.Tcs.IsEdgeGeodesicTransversal
import AFTD.Kb.Tcs.IsMaximalGeodesic

/-!
# exists_geodesic_transversal_of_edge_geodesic_transversal

Topic: graphs   Node: d50eb697744d

Provenance: helper lemma. scout/2610-36821-the-edge-geodesic-transversal-problem.md:107

For any finite edge geodesic transversal T in a simple graph G, there exists a finite vertex geodesic transversal S of G such that the cardinality of S is at most the cardinality of T.
-/

/-- From any finite edge geodesic transversal T, selecting one endpoint per edge yields a finite vertex geodesic transversal S with |S| ≤ |T|. -/
theorem exists_geodesic_transversal_of_edge_geodesic_transversal {V : Type*} (G : SimpleGraph V) (T : Finset (Sym2 V)) (hT : is_edge_geodesic_transversal G T) : ∃ S : Finset V, is_geodesic_transversal G S ∧ S.card ≤ T.card := by
  classical
  have sym2_nonempty : ∀ e : Sym2 V, ∃ x : V, x ∈ e := by
    intro e
    induction e using Sym2.ind with
    | _ x y => exact ⟨x, by simp⟩
  let pt : Sym2 V → V := fun e => Classical.choose (sym2_nonempty e)
  have pt_mem : ∀ e : Sym2 V, pt e ∈ e := fun e => Classical.choose_spec (sym2_nonempty e)
  let S := Finset.image pt T
  refine ⟨S, ?_, Finset.card_image_le⟩
  intro u v p hp
  have hp' : p.IsPath ∧ p.length = G.dist u v ∧
      (∀ w, G.Adj w u → G.dist w v ≤ p.length) ∧
      (∀ w, G.Adj v w → G.dist u w ≤ p.length) := by
    unfold is_maximal_geodesic at hp
    tauto
  rcases hT.2 p hp' with ⟨e, heT, he_edges⟩
  refine ⟨pt e, Finset.mem_image_of_mem pt heT, ?_⟩
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges]
  exact Or.inr ⟨e, he_edges, pt_mem e⟩
