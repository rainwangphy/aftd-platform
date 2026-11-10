import AFTD.Prelude
import AFTD.Kb.Tcs.BipartiteComplementRegular
import AFTD.Kb.Tcs.BipartiteComplementConnected
import AFTD.Kb.Tcs.BipartiteComplementAdjCharpolyMul
import AFTD.Kb.Tcs.RegularBipartiteAdjCharpolyRootsContainPmDegree
import AFTD.Kb.Tcs.RegularAdjCharpolyRootAbsLe
import AFTD.Kb.Tcs.AdjacencyLambda2EqOfCharpolyRoots
import AFTD.Kb.Tcs.AdjacencyLambda2
import AFTD.Kb.Tcs.ThreeTokenK2nDominationNumberFourGe

/-!
# bipartite_complement_adj_spectrum_and_lambda2

Topic: graphs   Node: 0f7e8f07ffb6

Provenance: formalization of a published result. Source: arXiv:2611.00591, Lemma 4.1

Let H be an s-regular bipartite simple graph whose two parts V and W each have size m ≥ 2, and let G = K_{V,W} \ E(H) be its bipartite complement. Then G is (m − s)-regular, and there is a multiset M of 2m − 2 reals such that the eigenvalues of the adjacency matrix of H (roots of its characteristic polynomial, with multiplicity) are s, −s and M, while those of G are m − s, −(m − s) and M. Furthermore, if m > 2s, then G is connected and its second largest adjacency eigenvalue equals that of H.
-/

open scoped Classical in
theorem bipartite_complement_adj_spectrum_and_lambda2
    {V W : Type*} [Fintype V] [Fintype W]
    (m s : ℕ) (hm : 2 ≤ m) (hV : Fintype.card V = m) (hW : Fintype.card W = m)
    (H : SimpleGraph (V ⊕ W)) (hH_sub : H ≤ completeBipartiteGraph V W)
    (hH_reg : H.IsRegularOfDegree s) :
    let G := completeBipartiteGraph V W \ H
    G.IsRegularOfDegree (m - s) ∧
    (∃ M : Multiset ℝ,
      Multiset.card M = 2 * m - 2 ∧
      (H.adjMatrix ℝ).charpoly.roots = {(s : ℝ), -(s : ℝ)} + M ∧
      (G.adjMatrix ℝ).charpoly.roots = {((m - s : ℕ) : ℝ), -((m - s : ℕ) : ℝ)} + M) ∧
    (2 * s < m → G.Connected ∧ adjacency_lambda2 G = adjacency_lambda2 H) := by
  intro G
  have hreg := bipartite_complement_regular m s hV hW H hH_sub hH_reg
  have hid := bipartite_complement_adj_charpoly_mul m s hV hW H hH_sub hH_reg
  have hB := regular_bipartite_adj_charpoly_roots_contain_pm_degree m s (by omega) hV hW H
    hH_sub hH_reg
  have hsm : s ≤ m := by
    obtain ⟨v0⟩ : Nonempty V := by
      rw [← Fintype.card_pos_iff]; omega
    have h1 : H.degree (Sum.inl v0) = s := hH_reg _
    have h2 : H.neighborFinset (Sum.inl v0) ⊆ Finset.univ.map Function.Embedding.inr := by
      intro x hx
      rw [SimpleGraph.mem_neighborFinset] at hx
      have := hH_sub hx
      rcases x with v | w
      · simp at this
      · simp
    have := Finset.card_le_card h2
    rw [Finset.card_map, Finset.card_univ, hW] at this
    rw [← h1]; exact this
  have hcardH : Multiset.card (H.adjMatrix ℝ).charpoly.roots = 2 * m := by
    rw [(H.isHermitian_adjMatrix ℝ).roots_charpoly_eq_eigenvalues]
    simp [hV, hW]; ring
  have hroots2 : ∀ c : ℝ, (Polynomial.X ^ 2 - Polynomial.C (c ^ 2) : Polynomial ℝ).roots =
      {c, -c} := by
    intro c
    have : (Polynomial.X ^ 2 - Polynomial.C (c ^ 2) : Polynomial ℝ) =
        (Polynomial.X - Polynomial.C c) * (Polynomial.X - Polynomial.C (-c)) := by
      rw [Polynomial.C_neg, map_pow]; ring
    rw [this, Polynomial.roots_mul ((Polynomial.monic_X_sub_C c).mul
      (Polynomial.monic_X_sub_C _)).ne_zero, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
    rfl
  have hsum : (G.adjMatrix ℝ).charpoly.roots + {(s : ℝ), -(s : ℝ)} =
      (H.adjMatrix ℝ).charpoly.roots + {((m : ℝ) - s), -((m : ℝ) - s)} := by
    have := congrArg Polynomial.roots hid
    rw [Polynomial.roots_mul, Polynomial.roots_mul, hroots2, hroots2] at this
    · exact this
    · exact ((Matrix.charpoly_monic _).mul (Polynomial.monic_X_pow_sub_C _ (by norm_num))).ne_zero
    · exact ((Matrix.charpoly_monic _).mul (Polynomial.monic_X_pow_sub_C _ (by norm_num))).ne_zero
  set M := (H.adjMatrix ℝ).charpoly.roots - {(s : ℝ), -(s : ℝ)} with hMdef
  have hHM : (H.adjMatrix ℝ).charpoly.roots = {(s : ℝ), -(s : ℝ)} + M :=
    (add_tsub_cancel_of_le hB).symm
  have hGM : (G.adjMatrix ℝ).charpoly.roots = {((m - s : ℕ) : ℝ), -((m - s : ℕ) : ℝ)} + M := by
    rw [Nat.cast_sub hsm]
    have : (G.adjMatrix ℝ).charpoly.roots + {(s : ℝ), -(s : ℝ)} =
        ({((m : ℝ) - s), -((m : ℝ) - s)} + M) + {(s : ℝ), -(s : ℝ)} := by
      rw [hsum, hHM]; abel
    exact add_right_cancel this
  have hcardM : Multiset.card M = 2 * m - 2 := by
    have := congrArg Multiset.card hHM
    rw [hcardH, Multiset.card_add] at this
    simp at this
    omega
  refine ⟨hreg, ⟨M, hcardM, hHM, hGM⟩, ?_⟩
  intro hs2
  refine ⟨bipartite_complement_connected m s hm hV hW H hH_sub hH_reg hs2, ?_⟩
  have hMne : M ≠ 0 := by
    intro h
    rw [h] at hcardM
    simp at hcardM
    omega
  obtain ⟨x, hxM, hxmax⟩ := M.toFinset.exists_max_image id (Multiset.toFinset_nonempty.mpr hMne)
  rw [Multiset.mem_toFinset] at hxM
  replace hxmax : ∀ y ∈ M, y ≤ x := fun y hy => hxmax y (Multiset.mem_toFinset.mpr hy)
  have habs : ∀ y ∈ M, |y| ≤ s := by
    intro y hy
    have hy' : y ∈ (H.adjMatrix ℝ).charpoly.roots := by
      rw [hHM]; exact Multiset.mem_add.mpr (Or.inr hy)
    exact regular_adj_charpoly_root_abs_le H s hH_reg y (by convert hy')
  have hx := abs_le.mp (habs x hxM)
  have hM' := Multiset.cons_erase hxM
  have hsm' : (s : ℝ) < ((m - s : ℕ) : ℝ) := by
    rw [Nat.cast_sub hsm]
    have : (2 * s : ℝ) < m := by exact_mod_cast hs2
    linarith
  have hHr : (H.adjMatrix ℝ).charpoly.roots = (s : ℝ) ::ₘ x ::ₘ (-(s : ℝ) ::ₘ M.erase x) := by
    rw [hHM]
    conv_lhs => rw [← hM']
    simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
    abel
  have hGr : (G.adjMatrix ℝ).charpoly.roots =
      ((m - s : ℕ) : ℝ) ::ₘ x ::ₘ (-((m - s : ℕ) : ℝ) ::ₘ M.erase x) := by
    rw [hGM]
    conv_lhs => rw [← hM']
    simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
    abel
  have hlamH : adjacency_lambda2 H = x := by
    apply adjacency_lambda2_eq_of_charpoly_roots H s x (-(s : ℝ) ::ₘ M.erase x)
    · convert hHr
    · exact hx.2
    · intro y hy
      rcases Multiset.mem_cons.mp hy with rfl | hy
      · exact hx.1
      · exact hxmax y (Multiset.mem_of_mem_erase hy)
  have hlamG : adjacency_lambda2 G = x := by
    apply adjacency_lambda2_eq_of_charpoly_roots G ((m - s : ℕ) : ℝ) x
      (-((m - s : ℕ) : ℝ) ::ₘ M.erase x)
    · convert hGr
    · linarith [hx.2]
    · intro y hy
      rcases Multiset.mem_cons.mp hy with rfl | hy
      · linarith [hx.1]
      · exact hxmax y (Multiset.mem_of_mem_erase hy)
  rw [hlamG, hlamH]
