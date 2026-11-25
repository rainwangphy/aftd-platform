import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphPairStableActiveVertexAtLeastFiveTriangles
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumberInduceLe

/-!
# simple_graph_pair_stable_two_disjoint_books_six_vertex_kernel

Topic: graphs   Node: cd3bdaac80e2

Provenance: helper lemma. Pair-deletion preserving representative kernel for the two-book branch of the triangle-packing campaign.

If every triangle of a two-edge-stable finite graph is either inside a set S or has one outside vertex and one of two vertex-disjoint edges of S, at most six outside vertices can be retained so that the induced graph has the same triangle-packing number and remains two-edge-stable.
-/

open scoped Sym2

theorem simple_graph_pair_stable_two_disjoint_books_six_vertex_kernel_no_outside_triangle
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (a b c d : Fin n)
    (hS : ({a,b,c,d} : Finset (Fin n)) ⊆ S)
    (hclass : ∀ t : Finset (Fin n), G.IsNClique 3 t → t ⊆ S ∨ ∃ w, w ∉ S ∧ (t = {a,b,w} ∨ t = {c,d,w}))
    (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
      simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G)
    (w : Fin n) (hw : w ∉ S) :
    ¬ ∃ t : Finset (Fin n), G.IsNClique 3 t ∧ w ∈ t := by
  have ha : a ∈ S := hS (by simp)
  have hb : b ∈ S := hS (by simp)
  have hc : c ∈ S := hS (by simp)
  have hd : d ∈ S := hS (by simp)
  intro ⟨t, ht, hwt⟩
  have h5 := simple_graph_pair_stable_active_vertex_at_least_five_triangles n G w hstable ⟨t, ht, hwt⟩
  let inst1 : DecidablePred (fun t : Finset (Fin n) => G.IsNClique 3 t ∧ w ∈ t) :=
    fun x => @instDecidableAnd (G.IsNClique 3 x) (w ∈ x)
      G.instDecidableIsNCliqueOfDecidableEqOfDecidableRelAdj (Finset.decidableMem w x)
  let s : Finset (Finset (Fin n)) := @Finset.filter (Finset (Fin n)) (fun t => G.IsNClique 3 t ∧ w ∈ t) inst1 Finset.univ
  have h5' : 5 ≤ s.card := h5
  have h_sub : s ⊆ ({{a,b,w}, {c,d,w}} : Finset (Finset (Fin n))) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    rcases hu with ⟨-, hcl, hwu⟩
    rcases hclass u hcl with huS | ⟨w', hw', huw'⟩
    · exfalso
      exact hw (huS hwu)
    · rcases huw' with rfl | rfl
      · have : w = w' := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwu
          rcases hwu with rfl | rfl | rfl
          · contradiction
          · contradiction
          · rfl
        subst this
        simp
      · have : w = w' := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwu
          rcases hwu with rfl | rfl | rfl
          · contradiction
          · contradiction
          · rfl
        subst this
        simp
  have h_two : ({{a,b,w}, {c,d,w}} : Finset (Finset (Fin n))).card ≤ 2 := by
    have : ({{a,b,w}, {c,d,w}} : Finset (Finset (Fin n))) = insert {a,b,w} {{c,d,w}} := rfl
    rw [this]
    exact (Finset.card_insert_le _ _).trans (by simp)
  have h_le := Finset.card_le_card h_sub
  omega

theorem simple_graph_pair_stable_two_disjoint_books_six_vertex_kernel_packing_num_induce_eq
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (h_all : ∀ t : Finset (Fin n), G.IsNClique 3 t → t ⊆ S) :
    simple_graph_triangle_packing_number (G.induce (S : Set (Fin n))) =
      simple_graph_triangle_packing_number G := by
  classical
  apply le_antisymm (simple_graph_triangle_packing_number_induce_le G S)
  unfold simple_graph_triangle_packing_number
  apply csSup_le
  · exact ⟨0, ∅, by simp, by simp, rfl⟩
  · rintro k ⟨T, hT, hTp, rfl⟩
    let f : Finset (Fin n) → Finset S := fun t => t.subtype (fun x => x ∈ S)
    let emb : S ↪ Fin n := Function.Embedding.subtype (fun x => x ∈ S)
    let U := T.image f
    have hsub : ∀ t ∈ T, ∀ x ∈ t, x ∈ S := by
      intro t ht x hx
      exact h_all t (hT t ht) hx
    have hmap : ∀ t ∈ T, (f t).map emb = t := by
      intro t ht
      exact Finset.subtype_map_of_mem (hsub t ht)
    have hinj : Set.InjOn f T := by
      intro a ha b hb hab
      have heq := congrArg (fun t : Finset S => t.map emb) hab
      rw [hmap a ha, hmap b hb] at heq
      exact heq
    have hcard : U.card = T.card := Finset.card_image_iff.mpr hinj
    have hc : ∀ t ∈ U, (G.induce (S : Set (Fin n))).IsNClique 3 t := by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      apply (G.isNClique_induce_iff (S : Set (Fin n)) (f s) 3).mpr
      change G.IsNClique 3 ((f s).map emb)
      rw [hmap s hs]
      exact hT s hs
    have hp : (U : Set (Finset S)).Pairwise (fun s t => (s ∩ t).card ≤ 1) := by
      intro s hs t ht hne
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
      have hne' : s' ≠ t' := by intro h; exact hne (congrArg f h)
      have h := hTp hs' ht' hne'
      have hi : ((f s' ∩ f t').map emb).card = (s' ∩ t').card := by
        rw [Finset.map_inter, hmap s' hs', hmap t' ht']
      simpa using hi.trans_le h
    apply le_csSup
    · refine ⟨Fintype.card (Finset S), ?_⟩
      rintro m ⟨P, _, _, rfl⟩
      exact Finset.card_le_univ P
    · exact ⟨U, hc, hp, hcard⟩

theorem simple_graph_pair_stable_two_disjoint_books_six_vertex_kernel_induce_deleteEdges
    {V : Type*} (G : SimpleGraph V) (s : Set V) (e f : Sym2 s) :
    (G.induce s).deleteEdges {e, f} =
      (G.deleteEdges {Sym2.map Subtype.val e, Sym2.map Subtype.val f}).induce s := by
  ext ⟨u, hu⟩ ⟨v, hv⟩
  rw [SimpleGraph.deleteEdges_adj, SimpleGraph.induce_adj, SimpleGraph.induce_adj,
      SimpleGraph.deleteEdges_adj]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hadj, hnot⟩
    refine ⟨hadj, ?_⟩
    rintro (h1 | h2)
    · apply hnot
      left
      exact Sym2.map.injective Subtype.val_injective h1
    · apply hnot
      right
      exact Sym2.map.injective Subtype.val_injective h2
  · rintro ⟨hadj, hnot⟩
    refine ⟨hadj, ?_⟩
    rintro (h1 | h2)
    · apply hnot
      left
      rw [← h1]
      rfl
    · apply hnot
      right
      rw [← h2]
      rfl

theorem simple_graph_pair_stable_two_disjoint_books_six_vertex_kernel (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) (a b c d : Fin n) (habcd : ({a,b,c,d} : Finset (Fin n)).card = 4) (hS : ({a,b,c,d} : Finset (Fin n)) ⊆ S) (hclass : ∀ t : Finset (Fin n), G.IsNClique 3 t → t ⊆ S ∨ ∃ w, w ∉ S ∧ (t = {a,b,w} ∨ t = {c,d,w})) (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f → simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G) : ∃ U : Finset (Fin n), Disjoint U S ∧ U.card ≤ 6 ∧ let H := G.induce (↑(S ∪ U) : Set (Fin n)); simple_graph_triangle_packing_number H = simple_graph_triangle_packing_number G ∧ ∀ e f : Sym2 {v : Fin n // v ∈ S ∪ U}, e ∈ H.edgeSet → f ∈ H.edgeSet → e ≠ f → simple_graph_triangle_packing_number (H.deleteEdges {e,f}) = simple_graph_triangle_packing_number H := by
  have hall : ∀ t : Finset (Fin n), G.IsNClique 3 t → t ⊆ S := by
    intro t ht
    rcases hclass t ht with htS | ⟨w, hw, hw_or⟩
    · exact htS
    · exfalso
      have hwt : w ∈ t := by rcases hw_or with rfl | rfl <;> simp
      exact simple_graph_pair_stable_two_disjoint_books_six_vertex_kernel_no_outside_triangle
        n G S a b c d hS hclass hstable w hw ⟨t, ht, hwt⟩
  refine ⟨∅, Finset.disjoint_empty_left S, by simp, ?_⟩
  dsimp
  have hSU : (S ∪ ∅ : Finset (Fin n)) = S := Finset.union_empty S
  have hSU_coe : (↑(S ∪ (∅ : Finset (Fin n))) : Set (Fin n)) = (↑S : Set (Fin n)) := by rw [hSU]
  have h_H_pack : simple_graph_triangle_packing_number (G.induce (↑(S ∪ ∅) : Set (Fin n))) =
      simple_graph_triangle_packing_number G := by
    rw [hSU_coe]
    exact simple_graph_pair_stable_two_disjoint_books_six_vertex_kernel_packing_num_induce_eq n G S hall
  refine ⟨h_H_pack, ?_⟩
  intro e f he hf hne
  have he_G : Sym2.map Subtype.val e ∈ G.edgeSet := by
    induction' e using Sym2.inductionOn with u v
    simp only [SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj] at he
    rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
    exact he
  have hf_G : Sym2.map Subtype.val f ∈ G.edgeSet := by
    induction' f using Sym2.inductionOn with u v
    simp only [SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj] at hf
    rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
    exact hf
  have hne_G : Sym2.map Subtype.val e ≠ Sym2.map Subtype.val f :=
    (Sym2.map.injective Subtype.val_injective).ne hne
  have h_del_pack := hstable (Sym2.map Subtype.val e) (Sym2.map Subtype.val f) he_G hf_G hne_G
  have hall_del : ∀ t, (G.deleteEdges {Sym2.map Subtype.val e, Sym2.map Subtype.val f}).IsNClique 3 t →
      t ⊆ (S ∪ ∅ : Finset (Fin n)) := by
    intro t ht
    rw [hSU]
    exact hall t (SimpleGraph.IsNClique.mono (SimpleGraph.deleteEdges_le _) ht)
  have h_ind_eq := simple_graph_pair_stable_two_disjoint_books_six_vertex_kernel_packing_num_induce_eq
    n (G.deleteEdges {Sym2.map Subtype.val e, Sym2.map Subtype.val f}) (S ∪ ∅) hall_del
  rw [simple_graph_pair_stable_two_disjoint_books_six_vertex_kernel_induce_deleteEdges]
  exact h_ind_eq.trans (h_del_pack.trans h_H_pack.symm)
