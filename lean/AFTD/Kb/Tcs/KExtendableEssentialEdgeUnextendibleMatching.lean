import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.MatchingVerticesCardAtMostTwiceEdges
import AFTD.Kb.Tcs.Op2037SubgraphFintype

/-!
# k_extendable_essential_edge_unextendible_matching

Topic: graphs   Node: 3808a3ceba46

Provenance: helper lemma. OP-1957: reusable extraction of a matching witness from minimality, needed before applying any residual-graph obstruction.

If G is k-extendable and deleting edge e destroys k-extendability, then a k-matching remains after the deletion but fails to extend to a perfect matching.
-/

theorem k_extendable_essential_edge_unextendible_matching
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ)
    (hG : is_k_extendable G k) (e : Sym2 V) (he : e ∈ G.edgeSet)
    (hessential : ¬ is_k_extendable (G.deleteEdges {e}) k) :
    ∃ M : (G.deleteEdges {e}).Subgraph,
      M.IsMatching ∧ M.edgeSet.ncard = k ∧
      ¬ ∃ P : (G.deleteEdges {e}).Subgraph, P.IsPerfectMatching ∧ M ≤ P := by
  classical
  induction e using Sym2.ind with
  | _ u v =>
   have huv : G.Adj u v := G.mem_edgeSet.mp he
   obtain ⟨hcard, ⟨M0, hM0, hM0k⟩, hext⟩ := hG
   have hG' : ∀ x y : V, (G.deleteEdges {s(u, v)}).Adj x y ↔ G.Adj x y ∧ s(x, y) ≠ s(u, v) := by
     intro x y
     simp [SimpleGraph.deleteEdges_adj]
   have hsym : ∀ x y : V, s(x, y) = s(u, v) → (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
     intro x y h
     simpa [Sym2.eq_iff] using h
   have huvne : u ≠ v := huv.ne
   -- (b) a k-matching of G - uv
   have hb : ∃ M : (G.deleteEdges {s(u, v)}).Subgraph, M.IsMatching ∧ M.edgeSet.ncard = k := by
     have hM0u : ∀ {x y y' : V}, M0.Adj x y → M0.Adj x y' → y = y' := by
       intro x y y' h h'
       exact (hM0 (M0.edge_vert h)).unique h h'
     by_cases hM0uv : M0.Adj u v
     · obtain ⟨P0, hP0, hM0P0⟩ := hext M0 hM0 hM0k
       have hP0' := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP0
       obtain ⟨S0, hS0, hS0c⟩ := matching_vertices_card_at_most_twice_edges M0 hM0 hM0k
       obtain ⟨w, hw⟩ : ∃ w : V, w ∉ S0 := by
         by_contra hall
         simp only [not_exists, not_not] at hall
         have h1 : S0 = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
         rw [h1, Finset.card_univ] at hS0c
         omega
       have hwM : w ∉ M0.verts := fun h => hw (hS0 w h)
       obtain ⟨w', hww', -⟩ := hP0' w
       have hw'M : w' ∉ M0.verts := by
         intro h
         obtain ⟨c, hc, -⟩ := hM0 h
         have : c = w := (hP0' w').unique (hM0P0.2 hc) hww'.symm
         exact hwM (this ▸ M0.edge_vert hc.symm)
       have hwne : w ≠ w' := (P0.adj_sub hww').ne
       have huM : u ∈ M0.verts := M0.edge_vert hM0uv
       have hvM : v ∈ M0.verts := M0.edge_vert hM0uv.symm
       have hwu : w ≠ u := fun h => hwM (h ▸ huM)
       have hwv : w ≠ v := fun h => hwM (h ▸ hvM)
       -- an M0-edge other than uv avoids u and v
       have hoff : ∀ {x y : V}, M0.Adj x y → s(x, y) ≠ s(u, v) → x ≠ u ∧ x ≠ v := by
         intro x y hxy hne
         constructor
         · rintro rfl
           exact hne (by rw [hM0u hxy hM0uv])
         · rintro rfl
           exact hne (by rw [hM0u hxy hM0uv.symm]; exact Sym2.eq_swap)
       let M1 : (G.deleteEdges {s(u, v)}).Subgraph :=
         { verts := (M0.verts \ {u, v}) ∪ {w, w'}
           Adj := fun x y => (M0.Adj x y ∧ s(x, y) ≠ s(u, v)) ∨ (x = w ∧ y = w') ∨ (x = w' ∧ y = w)
           adj_sub := by
             rintro x y (⟨h, hne⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
             · exact (hG' x y).mpr ⟨M0.adj_sub h, hne⟩
             · refine (hG' _ _).mpr ⟨P0.adj_sub hww', fun he => ?_⟩
               rcases hsym _ _ he with ⟨h1, -⟩ | ⟨h1, -⟩
               · exact hwu h1
               · exact hwv h1
             · refine (hG' _ _).mpr ⟨P0.adj_sub hww'.symm, fun he => ?_⟩
               rcases hsym _ _ he with ⟨-, h1⟩ | ⟨-, h1⟩
               · exact hwv h1
               · exact hwu h1
           edge_vert := by
             rintro x y (⟨h, hne⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
             · obtain ⟨h1, h2⟩ := hoff h hne
               exact Or.inl ⟨M0.edge_vert h, by simp [h1, h2]⟩
             · exact Or.inr (by simp)
             · exact Or.inr (by simp)
           symm := by
             refine ⟨?_⟩
             rintro x y (⟨h, hne⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
             · exact Or.inl ⟨h.symm, by rwa [Sym2.eq_swap]⟩
             · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
             · exact Or.inr (Or.inl ⟨rfl, rfl⟩) }
       refine ⟨M1, ?_, ?_⟩
       · intro x hx
         rcases hx with ⟨hx0, hxuv⟩ | hxw
         · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hxuv
           obtain ⟨y, hy, -⟩ := hM0 hx0
           have hne : s(x, y) ≠ s(u, v) := by
             intro he
             rcases hsym _ _ he with ⟨h1, -⟩ | ⟨h1, -⟩
             · exact hxuv.1 h1
             · exact hxuv.2 h1
           refine ⟨y, Or.inl ⟨hy, hne⟩, ?_⟩
           rintro y' (⟨h', -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
           · exact hM0u h' hy
           · exact absurd hx0 hwM
           · exact absurd hx0 hw'M
         · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxw
           rcases hxw with rfl | rfl
           · refine ⟨w', Or.inr (Or.inl ⟨rfl, rfl⟩), ?_⟩
             rintro y' (⟨h', -⟩ | ⟨-, rfl⟩ | ⟨h1, -⟩)
             · exact absurd (M0.edge_vert h') hwM
             · rfl
             · exact absurd h1 hwne
           · refine ⟨w, Or.inr (Or.inr ⟨rfl, rfl⟩), ?_⟩
             rintro y' (⟨h', -⟩ | ⟨h1, -⟩ | ⟨-, rfl⟩)
             · exact absurd (M0.edge_vert h') hw'M
             · exact absurd h1.symm hwne
             · rfl
       · have hE : M1.edgeSet = (M0.edgeSet \ {s(u, v)}) ∪ {s(w, w')} := by
           ext e
           induction e using Sym2.ind with
           | h x y =>
             simp only [SimpleGraph.Subgraph.mem_edgeSet, Set.mem_union, Set.mem_sdiff,
               Set.mem_singleton_iff]
             show ((M0.Adj x y ∧ s(x, y) ≠ s(u, v)) ∨ (x = w ∧ y = w') ∨ (x = w' ∧ y = w)) ↔ _
             simp only [Sym2.eq_iff, ne_eq]
         have hdisj : Disjoint (M0.edgeSet \ {s(u, v)}) {s(w, w')} := by
           rw [Set.disjoint_singleton_right]
           rintro ⟨h, -⟩
           exact hwM (M0.edge_vert h)
         have hmem : s(u, v) ∈ M0.edgeSet := hM0uv
         rw [hE, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
           Set.ncard_sdiff_singleton_of_mem hmem, Set.ncard_singleton, hM0k]
         have hpos : 0 < M0.edgeSet.ncard := Set.ncard_pos (Set.toFinite _) |>.mpr ⟨_, hmem⟩
         omega
     · refine ⟨⟨M0.verts, M0.Adj, fun {x y} h => (hG' x y).mpr ⟨M0.adj_sub h, fun he => ?_⟩,
         M0.edge_vert, M0.symm⟩, fun x hx => hM0 hx, ?_⟩
       · rcases hsym _ _ he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
         · exact hM0uv h
         · exact hM0uv h.symm
       · refine Eq.trans (congrArg Set.ncard ?_) hM0k
         ext e; induction e using Sym2.ind; exact Iff.rfl

   by_contra hcon
   push Not at hcon
   exact hessential ⟨hcard, hb, fun M hM hk => hcon M hM hk⟩
