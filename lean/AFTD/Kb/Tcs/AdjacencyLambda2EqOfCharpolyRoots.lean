import AFTD.Prelude
import AFTD.Kb.Tcs.AdjacencyLambda2

/-!
# adjacency_lambda2_eq_of_charpoly_roots

Topic: graphs   Node: ad5d50a43178

Provenance: helper lemma. arXiv:2611.00591, Lemma 4.1 (step of its proof)

For a simple graph G on a finite vertex set, if the roots of the characteristic polynomial of its real adjacency matrix are a, x and a multiset M with x ≤ a and every element of M at most x, then the second largest adjacency eigenvalue adjacency_lambda2 G equals x.
-/

open scoped Classical in
theorem adjacency_lambda2_eq_of_charpoly_roots
    {V : Type*} [Fintype V] (G : SimpleGraph V) (a x : ℝ) (M : Multiset ℝ)
    (hroots : (G.adjMatrix ℝ).charpoly.roots = a ::ₘ x ::ₘ M)
    (hxa : x ≤ a) (hM : ∀ y ∈ M, y ≤ x) :
    adjacency_lambda2 G = x := by
  have hA := G.isHermitian_adjMatrix ℝ
  have hsort := hA.sort_roots_charpoly_eq_eigenvalues₀
  have hre : (G.adjMatrix ℝ).charpoly.roots.map RCLike.re =
      (G.adjMatrix ℝ).charpoly.roots := by
    conv_rhs => rw [← Multiset.map_id (G.adjMatrix ℝ).charpoly.roots]
    rfl
  rw [hre, hroots, Multiset.sort_cons, Multiset.sort_cons] at hsort
  · have hlen := congrArg List.length hsort
    simp only [List.length_cons, List.length_ofFn] at hlen
    have hn : 2 ≤ Fintype.card V := by omega
    unfold adjacency_lambda2
    rw [dif_pos hn]
    have := congrArg (fun l => l[1]?) hsort
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, List.getElem?_ofFn] at this
    simp at this
    obtain ⟨_, hx⟩ := this
    exact hx.symm
  · exact fun b hb => hM b hb
  · intro b hb
    rcases Multiset.mem_cons.mp hb with rfl | hb
    · exact hxa
    · exact (hM b hb).trans hxa
