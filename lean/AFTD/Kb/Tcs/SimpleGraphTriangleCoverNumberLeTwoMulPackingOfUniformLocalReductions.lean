import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumberEqZeroOfCliqueFree
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumberLeTwoMulPackingOfLocalCertificate

/-!
# simple_graph_triangle_cover_number_le_two_mul_packing_of_uniform_local_reductions

Topic: graphs   Node: f292a6364039

Provenance: helper lemma. Structural induction for the triangle packing and covering problem; related work is arXiv:2610.15269, Lemma 2.2. No bound is imposed on the size of a reduction.

If every finite graph containing a triangle has a proper subgraph and a local packing-cover certificate that extends every packing of that subgraph, then every finite graph satisfies the triangle cover-packing inequality.
-/

theorem simple_graph_triangle_cover_number_le_two_mul_packing_of_uniform_local_reductions (hstep : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ¬ G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin n)) (S : Finset (Finset (Fin n))) (X : Finset (Sym2 (Fin n))), H ≤ G ∧ H ≠ G ∧ (∀ s ∈ S, G.IsNClique 3 s) ∧ (S : Set (Finset (Fin n))).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ (∀ s ∈ S, ∀ t : Finset (Fin n), H.IsNClique 3 t → (s ∩ t).card ≤ 1) ∧ (∀ e ∈ X, e ∈ G.edgeSet) ∧ (∀ t : Finset (Fin n), G.IsNClique 3 t → H.IsNClique 3 t ∨ ∃ e ∈ X, ∀ x ∈ e, x ∈ t) ∧ X.card ≤ 2 * S.card) : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), simple_graph_triangle_cover_number G ≤ 2 * simple_graph_triangle_packing_number G := by
  classical
  intro n G
  have key : ∀ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      Nat.card G.edgeSet = k →
      simple_graph_triangle_cover_number G ≤ 2 * simple_graph_triangle_packing_number G := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro n G hk
      by_cases hcf : G.CliqueFree 3
      · rw [simple_graph_triangle_cover_number_eq_zero_of_clique_free G hcf]
        exact Nat.zero_le _
      · obtain ⟨H, S, X, hsub, hne, hs, hsp, hsep, hx, hcover, hbudget⟩ := hstep n G hcf
        have hlt : Nat.card H.edgeSet < Nat.card G.edgeSet := by
          haveI : Fintype ↑H.edgeSet := Set.Finite.fintype (Set.toFinite _)
          haveI : Fintype ↑G.edgeSet := Set.Finite.fintype (Set.toFinite _)
          rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
          rw [← SimpleGraph.edgeFinset_card, ← SimpleGraph.edgeFinset_card]
          have hlt' : H < G := lt_of_le_of_ne hsub hne
          exact Finset.card_lt_card ((SimpleGraph.edgeFinset_ssubset_edgeFinset).mpr hlt')
        have hind : simple_graph_triangle_cover_number H ≤
            2 * simple_graph_triangle_packing_number H :=
          ih (Nat.card H.edgeSet) (by omega) n H rfl
        exact simple_graph_triangle_cover_number_le_two_mul_packing_of_local_certificate
          G H hsub S X hs hsp hsep hx hcover hbudget hind
  exact key (Nat.card G.edgeSet) n G rfl
