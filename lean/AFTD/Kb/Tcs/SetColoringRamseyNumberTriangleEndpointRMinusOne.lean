import AFTD.Prelude
import AFTD.Kb.Tcs.SetColoringRamseyNumber
import AFTD.Kb.Tcs.MulticolorRamseyNumber
import AFTD.Kb.Tcs.MonoColorSubgraph
import AFTD.Kb.Tcs.MulticolorRamseyProperty
import AFTD.Kb.Tcs.SupportGraph
import AFTD.Kb.Tcs.SetColoringRamseyProperty
import AFTD.Kb.Tcs.G

/-!
# set_coloring_ramsey_number_triangle_endpoint_r_minus_one

Topic: combinatorics   Node: afc6dbb06836

Provenance: formalization of a published result. Source: arXiv:2611.19312 Proposition 1 (iii)

For every integer r ≥ 3, the set-coloring Ramsey number of the triangle with palette parameters r, r - 1 and intersection parameter t = r - 1 satisfies R(3; r, r-1, r-1) = R(3; r), the multicolor Ramsey number of the triangle with r colors.
-/

open scoped Classical

lemma set_coloring_ramsey_number_triangle_endpoint_r_minus_one_compl_singleton_eq {r : ℕ}
    {φ : Finset (Fin r)} {a : Fin r} (h : φᶜ = {a}) : φ = Finset.univ.erase a := by
  have hcompl : (φᶜ)ᶜ = φ := by ext x; simp
  calc φ = (φᶜ)ᶜ := hcompl.symm
    _ = ({a} : Finset (Fin r))ᶜ := by rw [h]
    _ = Finset.univ.erase a := Finset.compl_singleton a

lemma set_coloring_ramsey_number_triangle_endpoint_r_minus_one_exists_compl_singleton {r : ℕ}
    (hr : 1 ≤ r) (φ : Finset (Fin r)) (hφ : φ.card = r - 1) : ∃ a : Fin r, φᶜ = {a} := by
  have hcard : φᶜ.card = 1 := by
    rw [Finset.card_compl, Fintype.card_fin, hφ]
    omega
  exact Finset.card_eq_one.mp hcard

lemma set_coloring_ramsey_number_triangle_endpoint_r_minus_one_support_graph_adj_iff
    {V : Type*} {r : ℕ} (φ : (⊤ : SimpleGraph V).edgeSet → Finset (Fin r)) (T : Finset (Fin r))
    {u v : V} :
    (support_graph φ T).Adj u v ↔
      (∃ h : s(u, v) ∈ (⊤ : SimpleGraph V).edgeSet, T ⊆ φ ⟨s(u, v), h⟩) ∧ u ≠ v := by
  rw [support_graph, SimpleGraph.fromEdgeSet_adj]
  simp only [Set.mem_ofPred_eq]

lemma set_coloring_ramsey_number_triangle_endpoint_r_minus_one_mono_color_subgraph_adj_iff
    {V : Type*} {C : Type*} (c : (⊤ : SimpleGraph V).edgeSet → C) (col : C) {u v : V} :
    (mono_color_subgraph (⊤ : SimpleGraph V) c col).Adj u v ↔
      (∃ h : s(u, v) ∈ (⊤ : SimpleGraph V).edgeSet, c ⟨s(u, v), h⟩ = col) ∧ u ≠ v := by
  rw [mono_color_subgraph, SimpleGraph.fromEdgeSet_adj]
  simp only [Set.mem_ofPred_eq]

lemma set_coloring_ramsey_number_triangle_endpoint_r_minus_one_eq_of_card_pred_not_mem
    {r : ℕ} (hr : 1 ≤ r) {T : Finset (Fin r)} (hT : T.card = r - 1) {a b : Fin r}
    (ha : a ∉ T) (hb : b ∉ T) : a = b := by
  have hcard : (insert a T).card = r := by
    rw [Finset.card_insert_of_notMem ha, hT]; omega
  have huniv : insert a T = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard, Fintype.card_fin]
  have : b ∈ insert a T := by rw [huniv]; exact Finset.mem_univ _
  rcases Finset.mem_insert.mp this with h | h
  · exact h.symm
  · exact absurd h hb

lemma set_coloring_ramsey_number_triangle_endpoint_r_minus_one_setcoloring_to_multicolor
    (r N : ℕ) (hr : 1 ≤ r)
    (h : set_coloring_ramsey_property (⊤ : SimpleGraph (Fin 3)) r (r - 1) (r - 1) N) :
    multicolor_ramsey_property (⊤ : SimpleGraph (Fin 3)) r N := by
  intro c
  let φ : (⊤ : SimpleGraph (Fin N)).edgeSet → Finset (Fin r) := fun e => Finset.univ.erase (c e)
  have hφ : ∀ e, (φ e).card = r - 1 := by
    intro e
    simp [φ, Finset.card_erase_of_mem (Finset.mem_univ (c e))]
  obtain ⟨T, hTcard, hcont⟩ := h φ hφ
  obtain ⟨cc⟩ := hcont
  let f : (⊤ : SimpleGraph (Fin 3)) →g support_graph φ T := cc.toHom
  have hf_inj : Function.Injective f := cc.injective'
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have hadj01 : (⊤ : SimpleGraph (Fin 3)).Adj 0 1 := by
    simpa [SimpleGraph.top_adj] using h01
  have hsup01 := f.map_adj hadj01
  rw [set_coloring_ramsey_number_triangle_endpoint_r_minus_one_support_graph_adj_iff] at hsup01
  obtain ⟨⟨hE01, hsub01⟩, -⟩ := hsup01
  let col : Fin r := c ⟨s(f 0, f 1), hE01⟩
  have hcol : ∀ (i j : Fin 3) (hij : i ≠ j)
      (hE : s(f i, f j) ∈ (⊤ : SimpleGraph (Fin N)).edgeSet),
      T ⊆ φ ⟨s(f i, f j), hE⟩ → c ⟨s(f i, f j), hE⟩ = col := by
    intro i j hij hE hsub
    have hnot : c ⟨s(f i, f j), hE⟩ ∉ T := by
      intro hmem
      have hmem' : c ⟨s(f i, f j), hE⟩ ∈ φ ⟨s(f i, f j), hE⟩ := hsub hmem
      simp [φ] at hmem'
    have hnot01 : c ⟨s(f 0, f 1), hE01⟩ ∉ T := by
      intro hmem
      have hmem' : c ⟨s(f 0, f 1), hE01⟩ ∈ φ ⟨s(f 0, f 1), hE01⟩ := hsub01 hmem
      simp [φ] at hmem'
    have := set_coloring_ramsey_number_triangle_endpoint_r_minus_one_eq_of_card_pred_not_mem
      hr hTcard hnot hnot01
    simpa [col] using this
  refine ⟨col, ⟨SimpleGraph.Copy.mk ⟨fun x => f x, ?_⟩ hf_inj⟩⟩
  intro a b hab
  have habne : a ≠ b := by simpa [SimpleGraph.top_adj] using hab
  have hsup := f.map_adj hab
  rw [set_coloring_ramsey_number_triangle_endpoint_r_minus_one_support_graph_adj_iff] at hsup
  obtain ⟨⟨hE, hsub⟩, -⟩ := hsup
  rw [set_coloring_ramsey_number_triangle_endpoint_r_minus_one_mono_color_subgraph_adj_iff]
  exact ⟨⟨hE, hcol a b habne hE hsub⟩, hf_inj.ne habne⟩

lemma set_coloring_ramsey_number_triangle_endpoint_r_minus_one_multicolor_to_setcoloring
    (r N : ℕ) (hr : 1 ≤ r)
    (h : multicolor_ramsey_property (⊤ : SimpleGraph (Fin 3)) r N) :
    set_coloring_ramsey_property (⊤ : SimpleGraph (Fin 3)) r (r - 1) (r - 1) N := by
  intro φ hφ
  let miss : (⊤ : SimpleGraph (Fin N)).edgeSet → Fin r :=
    fun e => Classical.choose
      (set_coloring_ramsey_number_triangle_endpoint_r_minus_one_exists_compl_singleton hr (φ e) (hφ e))
  have hmiss_compl : ∀ e, (φ e)ᶜ = {miss e} :=
    fun e => Classical.choose_spec
      (set_coloring_ramsey_number_triangle_endpoint_r_minus_one_exists_compl_singleton hr (φ e) (hφ e))
  have hmiss_eq : ∀ e, φ e = Finset.univ.erase (miss e) :=
    fun e => set_coloring_ramsey_number_triangle_endpoint_r_minus_one_compl_singleton_eq
      (hmiss_compl e)
  obtain ⟨col, hcont⟩ := h miss
  obtain ⟨cc⟩ := hcont
  let f : (⊤ : SimpleGraph (Fin 3)) →g
      mono_color_subgraph (⊤ : SimpleGraph (Fin N)) miss col := cc.toHom
  have hf_inj : Function.Injective f := cc.injective'
  let T : Finset (Fin r) := Finset.univ.erase col
  have hTcard : T.card = r - 1 := by
    simp [T, Finset.card_erase_of_mem (Finset.mem_univ col)]
  refine ⟨T, hTcard, ⟨SimpleGraph.Copy.mk ⟨fun x => f x, ?_⟩ hf_inj⟩⟩
  intro u v huv
  have huvne : u ≠ v := by simpa [SimpleGraph.top_adj] using huv
  have hmono := f.map_adj huv
  rw [set_coloring_ramsey_number_triangle_endpoint_r_minus_one_mono_color_subgraph_adj_iff] at hmono
  obtain ⟨⟨hE, hcol⟩, -⟩ := hmono
  rw [set_coloring_ramsey_number_triangle_endpoint_r_minus_one_support_graph_adj_iff]
  refine ⟨⟨hE, ?_⟩, hf_inj.ne huvne⟩
  rw [hmiss_eq, hcol]

/-- R(3; r, r-1, r-1) = R(3; r). -/
theorem set_coloring_ramsey_number_triangle_endpoint_r_minus_one
    (r : ℕ) (hr : 3 ≤ r) :
    set_coloring_ramsey_number (⊤ : SimpleGraph (Fin 3)) r (r - 1) (r - 1) =
      multicolor_ramsey_number (⊤ : SimpleGraph (Fin 3)) r := by
  have hr1 : 1 ≤ r := by omega
  rw [set_coloring_ramsey_number, multicolor_ramsey_number]
  congr 1
  ext N
  exact ⟨set_coloring_ramsey_number_triangle_endpoint_r_minus_one_setcoloring_to_multicolor r N hr1,
    set_coloring_ramsey_number_triangle_endpoint_r_minus_one_multicolor_to_setcoloring r N hr1⟩
