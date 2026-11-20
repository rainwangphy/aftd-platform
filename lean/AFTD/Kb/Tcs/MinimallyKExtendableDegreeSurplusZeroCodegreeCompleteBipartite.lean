import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.ForcedMatchingEdgeCommonNonneighborsBelowMinDegreeIsBridge
import AFTD.Kb.Tcs.Op2037SubgraphFintype
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# minimally_k_extendable_degree_surplus_zero_codegree_complete_bipartite

Topic: graphs   Node: 4d60edb87552

Provenance: helper lemma. OP-1957: the general matching bridge obstruction supplies complete bipartite complement subgraphs; experiment 34644.

In a minimally k-extendable graph of minimum degree at least 2k+r, r at least two, every graph edge whose endpoints have no common complement neighbor has a complete bipartite complement graph with r vertices in each endpoint neighborhood.
-/

open SimpleGraph in
theorem in1068_transport {V : Type*} (G : SimpleGraph V) (u v : V)
    (M : (G.deleteEdges {s(u,v)}).Subgraph) (Q : G.Subgraph) (hQ : Q.IsPerfectMatching)
    (hMQv : M.verts ⊆ Q.verts) (hMQ : ∀ x y, M.Adj x y → Q.Adj x y) (hno : ¬ Q.Adj u v) :
    ∃ P : (G.deleteEdges {s(u,v)}).Subgraph, P.IsPerfectMatching ∧ M ≤ P := by
  have hsub : ∀ {x y : V}, Q.Adj x y → (G.deleteEdges {s(u,v)}).Adj x y := by
    intro x y h
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨Q.adj_sub h, ?_⟩
    intro he
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hno h
    · exact hno h.symm
  refine ⟨⟨Q.verts, Q.Adj, hsub, Q.edge_vert, Q.symm⟩, ⟨fun x hx => hQ.1 hx, fun x => hQ.2 x⟩, ?_⟩
  exact ⟨hMQv, fun {x y} h => hMQ x y h⟩

open SimpleGraph in
theorem in1068_verts_bound {n k : ℕ} {H : SimpleGraph (Fin n)} (M : H.Subgraph) (hM : M.IsMatching)
    (hMk : M.edgeSet.ncard = k) :
    ∃ S : Finset (Fin n), (∀ x, x ∈ M.verts → x ∈ S) ∧ S.card ≤ 2 * k := by
  classical
  refine ⟨(M.edgeSet.toFinite.toFinset).biUnion (fun e => e.toFinset), ?_, ?_⟩
  · intro x hx
    obtain ⟨w, hw, -⟩ := hM hx
    rw [Finset.mem_biUnion]
    exact ⟨s(x, w), by simpa using hw, by simp⟩
  · have h1 : ((M.edgeSet.toFinite.toFinset).biUnion (fun e => e.toFinset)).card ≤
        (M.edgeSet.toFinite.toFinset).card * 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro e _
      rw [Sym2.card_toFinset]
      split_ifs <;> omega
    have h2 : (M.edgeSet.toFinite.toFinset).card = k := by
      rw [← Set.ncard_eq_toFinset_card M.edgeSet M.edgeSet.toFinite, hMk]
    omega

theorem minimally_k_extendable_degree_surplus_zero_codegree_complete_bipartite
    (k n r : ℕ) (hr : 2 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hmin : is_minimally_k_extendable G k) (hdegree : 2*k+r ≤ G.minDegree)
    (u v : Fin n) (huv : G.Adj u v)
    (hfar2 : ∀ x, ¬ ((Gᶜ).Adj u x ∧ (Gᶜ).Adj v x)) :
    ∃ A B : Finset (Fin n), A.card = r ∧ B.card = r ∧
      (∀ a ∈ A, (Gᶜ).Adj u a) ∧ (∀ b ∈ B, (Gᶜ).Adj v b) ∧
      ∀ a ∈ A, ∀ b ∈ B, (Gᶜ).Adj a b := open SimpleGraph in by
  classical
  obtain ⟨⟨hcard, ⟨M0, hM0, hM0k⟩, hext⟩, hminimal⟩ := hmin
  have hG' : ∀ x y : Fin n, (G.deleteEdges {s(u, v)}).Adj x y ↔ G.Adj x y ∧ s(x, y) ≠ s(u, v) := by
    intro x y
    simp [SimpleGraph.deleteEdges_adj]
  have hsym : ∀ x y : Fin n, s(x, y) = s(u, v) → (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
    intro x y h
    simpa [Sym2.eq_iff] using h
  have huvne : u ≠ v := huv.ne
  -- (b) a k-matching of G - uv
  have hb : ∃ M : (G.deleteEdges {s(u, v)}).Subgraph, M.IsMatching ∧ M.edgeSet.ncard = k := by
    have hM0u : ∀ {x y y' : Fin n}, M0.Adj x y → M0.Adj x y' → y = y' := by
      intro x y y' h h'
      exact (hM0 (M0.edge_vert h)).unique h h'
    by_cases hM0uv : M0.Adj u v
    · obtain ⟨P0, hP0, hM0P0⟩ := hext M0 hM0 hM0k
      have hP0' := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP0
      obtain ⟨S0, hS0, hS0c⟩ := in1068_verts_bound M0 hM0 hM0k
      obtain ⟨w, hw⟩ : ∃ w : Fin n, w ∉ S0 := by
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
      have hoff : ∀ {x y : Fin n}, M0.Adj x y → s(x, y) ≠ s(u, v) → x ≠ u ∧ x ≠ v := by
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
  -- a non-extendable k-matching of G - uv
  have hnot := hminimal s(u, v) (by simpa using huv)
  obtain ⟨M, hM, hMk, hMno⟩ : ∃ M : (G.deleteEdges {s(u, v)}).Subgraph, M.IsMatching ∧
      M.edgeSet.ncard = k ∧ ¬ ∃ P : (G.deleteEdges {s(u, v)}).Subgraph, P.IsPerfectMatching ∧ M ≤ P := by
    by_contra hcon
    push Not at hcon
    exact hnot ⟨hcard, hb, fun M hM hk => hcon M hM hk⟩
  have hup : ∀ {x y : Fin n}, M.Adj x y → G.Adj x y := fun h => ((hG' _ _).mp (M.adj_sub h)).1
  let MG : G.Subgraph := ⟨M.verts, M.Adj, hup, M.edge_vert, M.symm⟩
  have hMG : MG.IsMatching := fun x hx => hM hx
  have hMGk : MG.edgeSet.ncard = k :=
    Eq.trans (congrArg Set.ncard (by ext e; induction e using Sym2.ind; exact Iff.rfl)) hMk
  obtain ⟨P, hP, hMP⟩ := hext MG hMG hMGk
  have hP' := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP
  have hMPadj : ∀ {x y : Fin n}, M.Adj x y → P.Adj x y := fun h => hMP.2 h
  have hPuv : P.Adj u v := by
    by_contra h
    exact hMno (in1068_transport G u v M P hP hMP.1 (fun x y hxy => hMPadj hxy) h)
  have hnotin : ∀ x, (x = u ∨ x = v) → x ∉ M.verts := by
    intro x hx hxM
    obtain ⟨y, hy, -⟩ := hM hxM
    have hPy := hMPadj hy
    rcases hx with rfl | rfl
    · have : y = v := (hP' x).unique hPy hPuv
      subst this
      exact ((hG' _ _).mp (M.adj_sub hy)).2 rfl
    · have : y = u := (hP' x).unique hPy hPuv.symm
      subst this
      exact ((hG' _ _).mp (M.adj_sub hy)).2 Sym2.eq_swap
  have huR : u ∉ M.verts := hnotin u (Or.inl rfl)
  have hvR : v ∉ M.verts := hnotin v (Or.inr rfl)
  have hcl : ∀ a b, P.Adj a b → a ∉ M.verts → b ∉ M.verts := by
    intro a b hab ha hbM
    obtain ⟨c, hc, -⟩ := hM hbM
    have : c = a := (hP' b).unique (hMPadj hc) hab.symm
    exact ha (this ▸ M.edge_vert hc.symm)
  obtain ⟨Sf, hSf, hSfc⟩ := in1068_verts_bound MG hMG hMGk
  -- many neighbours outside M
  have hbig : ∀ x : Fin n, r ≤ (G.neighborFinset x \ Sf).card := by
    intro x
    have h1 : 2 * k + r ≤ (G.neighborFinset x).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact le_trans hdegree (G.minDegree_le_degree x)
    have := Finset.le_card_sdiff Sf (G.neighborFinset x)
    omega
  have hout : ∀ y, y ∉ Sf → y ∉ M.verts := fun y hy hyM => hy (hSf y hyM)
  -- the residual graph
  let s : Set (Fin n) := {x | x ∉ M.verts}
  let Gr : SimpleGraph s := G.induce s
  have hGr : ∀ x y : s, Gr.Adj x y ↔ G.Adj x.1 y.1 := fun x y => Iff.rfl
  let uW : s := ⟨u, huR⟩
  let vW : s := ⟨v, hvR⟩
  let Gd := Gr.deleteEdges {s(uW, vW)}
  have hGd : ∀ x y : s, G.Adj x.1 y.1 → ¬ ((x.1 = u ∧ y.1 = v) ∨ (x.1 = v ∧ y.1 = u)) → Gd.Adj x y := by
    intro x y hxy hne
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hxy, ?_⟩
    intro he
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at he
    apply hne
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
    · exact Or.inr ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
  have hGdsub : ∀ x y : s, Gd.Adj x y → G.Adj x.1 y.1 := fun x y h => (SimpleGraph.deleteEdges_adj.mp h).1
  -- hypotheses of the forced-edge lemma on Gr
  have hdegGr : ∀ x : s, r ≤ Gr.degree x := by
    intro x
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hsub : G.neighborFinset x.1 \ Sf ⊆ (Gr.neighborFinset x).map ⟨Subtype.val, Subtype.val_injective⟩ := by
      intro y hy
      rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hy
      rw [Finset.mem_map]
      exact ⟨⟨y, hout y hy.2⟩, by rw [SimpleGraph.mem_neighborFinset]; exact hy.1, rfl⟩
    have := le_trans (hbig x.1) (Finset.card_le_card hsub)
    rwa [Finset.card_map] at this
  have hPGr : ∃ Pr : Gr.Subgraph, Pr.IsPerfectMatching ∧ Pr.Adj uW vW := by
    let Pr : Gr.Subgraph :=
      { verts := Set.univ
        Adj := fun x y => P.Adj x.1 y.1
        adj_sub := fun {x y} h => P.adj_sub h
        edge_vert := fun _ => Set.mem_univ _
        symm := ⟨fun x y h => h.symm⟩ }
    refine ⟨Pr, ?_, hPuv⟩
    rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
    intro x
    obtain ⟨p, hp, hpu⟩ := hP' x.1
    refine ⟨⟨p, hcl x.1 p hp x.2⟩, hp, fun y hy => Subtype.ext (hpu y.1 hy)⟩
  have hforcedGr : ¬ ∃ Q : Gd.Subgraph, Q.IsPerfectMatching := by
    rintro ⟨Q, hQ⟩
    have hQ' := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hQ
    apply hMno
    let Q' : (G.deleteEdges {s(u, v)}).Subgraph :=
      { verts := Set.univ
        Adj := fun x y => M.Adj x y ∨ ∃ hx : x ∉ M.verts, ∃ hy : y ∉ M.verts, Q.Adj ⟨x, hx⟩ ⟨y, hy⟩
        adj_sub := by
          rintro x y (h | ⟨hx, hy, h⟩)
          · exact M.adj_sub h
          · have h1 := Q.adj_sub h
            rw [SimpleGraph.deleteEdges_adj] at h1
            refine (hG' x y).mpr ⟨h1.1, fun he => h1.2 ?_⟩
            rw [Set.mem_singleton_iff, Sym2.eq_iff]
            rcases hsym _ _ he with ⟨h2, h3⟩ | ⟨h2, h3⟩
            · exact Or.inl ⟨Subtype.ext h2, Subtype.ext h3⟩
            · exact Or.inr ⟨Subtype.ext h2, Subtype.ext h3⟩
        edge_vert := fun _ => Set.mem_univ _
        symm := by
          refine ⟨?_⟩
          rintro x y (h | ⟨hx, hy, h⟩)
          · exact Or.inl h.symm
          · exact Or.inr ⟨hy, hx, h.symm⟩ }
    refine ⟨Q', ?_, ⟨fun _ _ => Set.mem_univ _, fun {x y} h => Or.inl h⟩⟩
    rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
    intro x
    by_cases hxM : x ∈ M.verts
    · obtain ⟨y, hy, hyu⟩ := hM hxM
      refine ⟨y, Or.inl hy, ?_⟩
      rintro y' (h | ⟨hx, -, -⟩)
      · exact hyu y' h
      · exact absurd hxM hx
    · obtain ⟨y, hy, hyu⟩ := hQ' ⟨x, hxM⟩
      refine ⟨y.1, Or.inr ⟨hxM, y.2, hy⟩, ?_⟩
      rintro y' (h | ⟨hx', hy', h⟩)
      · exact absurd (M.edge_vert h) hxM
      · exact congrArg Subtype.val (hyu ⟨y', hy'⟩ h)
  have hcoGr : ({w | (Grᶜ).Adj uW w ∧ (Grᶜ).Adj vW w} : Set s).ncard < r := by
    have hempty : ({w | (Grᶜ).Adj uW w ∧ (Grᶜ).Adj vW w} : Set s) = ∅ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2⟩
      rw [SimpleGraph.compl_adj] at h1 h2
      apply hfar2 w.1
      refine ⟨(SimpleGraph.compl_adj G u w.1).2 ⟨fun h => h1.1 (Subtype.ext h), h1.2⟩,
        (SimpleGraph.compl_adj G v w.1).2 ⟨fun h => h2.1 (Subtype.ext h), h2.2⟩⟩
    rw [hempty, Set.ncard_empty]
    omega
  have key := forced_matching_edge_common_nonneighbors_below_min_degree_is_bridge Gr r hdegGr uW vW
    huv hPGr hforcedGr hcoGr
  -- the two sides
  have hreachv : ∀ y : s, Gd.Reachable uW y → y.1 ≠ v := by
    intro y hy hyv
    apply key
    have : y = vW := Subtype.ext hyv
    rwa [this] at hy
  have hedge : ∀ x y : s, Gd.Reachable uW x → G.Adj x.1 y.1 → x.1 ≠ u ∨ y.1 ≠ v →
      x.1 ≠ v ∨ y.1 ≠ u → Gd.Reachable uW y := by
    intro x y hx hxy h1 h2
    refine hx.trans (SimpleGraph.Adj.reachable (hGd x y hxy ?_))
    rintro (⟨a, b⟩ | ⟨a, b⟩)
    · rcases h1 with h | h
      · exact h a
      · exact h b
    · rcases h2 with h | h
      · exact h a
      · exact h b
  let Bs : Finset (Fin n) := Finset.univ.filter (fun x => ∃ h : x ∉ M.verts, Gd.Reachable uW ⟨x, h⟩ ∧ x ≠ u)
  let As : Finset (Fin n) := Finset.univ.filter (fun x => ∃ h : x ∉ M.verts, ¬ Gd.Reachable uW ⟨x, h⟩ ∧ x ≠ v)
  -- properties
  have hBprop : ∀ b ∈ Bs, (Gᶜ).Adj v b := by
    intro b hb
    simp only [Bs, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨hbM, hbr, hbu⟩ := hb
    have hbv := hreachv _ hbr
    refine (SimpleGraph.compl_adj G v b).2 ⟨fun h => hbv h.symm, fun hvb => ?_⟩
    apply key
    have := hedge ⟨b, hbM⟩ vW hbr hvb.symm (Or.inl hbu) (Or.inl hbv)
    exact this
  have hAprop : ∀ a ∈ As, (Gᶜ).Adj u a := by
    intro a ha
    simp only [As, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨haM, har, hav⟩ := ha
    have hau : a ≠ u := by
      rintro rfl
      exact har (SimpleGraph.Reachable.refl _)
    refine (SimpleGraph.compl_adj G u a).2 ⟨fun h => hau h.symm, fun hua => ?_⟩
    exact har (hedge uW ⟨a, haM⟩ (SimpleGraph.Reachable.refl _) hua (Or.inr hav) (Or.inr hau))
  have hABprop : ∀ a ∈ As, ∀ b ∈ Bs, (Gᶜ).Adj a b := by
    intro a ha b hb
    simp only [As, Bs, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨haM, har, hav⟩ := ha
    obtain ⟨hbM, hbr, hbu⟩ := hb
    have hab : a ≠ b := by
      rintro rfl
      exact har hbr
    refine (SimpleGraph.compl_adj G a b).2 ⟨hab, fun hadj => ?_⟩
    exact har (hedge ⟨b, hbM⟩ ⟨a, haM⟩ hbr hadj.symm (Or.inl hbu) (Or.inl (hreachv _ hbr)))
  -- sizes
  have hBcard : r ≤ Bs.card := by
    obtain ⟨y, hy⟩ : ∃ y, y ∈ (G.neighborFinset u \ Sf).erase v := by
      apply Finset.card_pos.mp
      have := hbig u
      have := Finset.card_erase_le (s := G.neighborFinset u \ Sf) (a := v)
      have h2 := Finset.pred_card_le_card_erase (s := G.neighborFinset u \ Sf) (a := v)
      omega
    rw [Finset.mem_erase, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hy
    obtain ⟨hyv, huy, hyS⟩ := hy
    have hyM := hout y hyS
    have hyr : Gd.Reachable uW ⟨y, hyM⟩ :=
      hedge uW ⟨y, hyM⟩ (SimpleGraph.Reachable.refl _) huy (Or.inr hyv) (Or.inr (fun h => huy.ne h.symm))
    have hyu : y ≠ u := fun h => huy.ne h.symm
    have hsub : insert y (G.neighborFinset y \ Sf) ⊆ insert u Bs := by
      intro z hz
      rw [Finset.mem_insert] at hz ⊢
      rcases hz with rfl | hz
      · right
        simp only [Bs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hyM, hyr, hyu⟩
      · rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hz
        by_cases hzu : z = u
        · exact Or.inl hzu
        · right
          simp only [Bs, Finset.mem_filter, Finset.mem_univ, true_and]
          have hzM := hout z hz.2
          refine ⟨hzM, hedge ⟨y, hyM⟩ ⟨z, hzM⟩ hyr hz.1 (Or.inl hyu) (Or.inr hzu), hzu⟩
    have h1 := Finset.card_le_card hsub
    have hyn : y ∉ G.neighborFinset y \ Sf := by simp
    rw [Finset.card_insert_of_notMem hyn] at h1
    have h2 := Finset.card_insert_le u Bs
    have := hbig y
    omega
  have hAcard : r ≤ As.card := by
    obtain ⟨y, hy⟩ : ∃ y, y ∈ (G.neighborFinset v \ Sf).erase u := by
      apply Finset.card_pos.mp
      have := hbig v
      have h2 := Finset.pred_card_le_card_erase (s := G.neighborFinset v \ Sf) (a := u)
      omega
    rw [Finset.mem_erase, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hy
    obtain ⟨hyu, hvy, hyS⟩ := hy
    have hyM := hout y hyS
    have hyv : y ≠ v := fun h => hvy.ne h.symm
    -- y is not reachable: otherwise v would be
    have hyr : ¬ Gd.Reachable uW ⟨y, hyM⟩ := by
      intro h
      apply key
      exact hedge ⟨y, hyM⟩ vW h hvy.symm (Or.inl hyu) (Or.inl hyv)
    have hsub : insert y (G.neighborFinset y \ Sf) ⊆ insert v As := by
      intro z hz
      rw [Finset.mem_insert] at hz ⊢
      rcases hz with rfl | hz
      · right
        simp only [As, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hyM, hyr, hyv⟩
      · rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hz
        by_cases hzv : z = v
        · exact Or.inl hzv
        · right
          simp only [As, Finset.mem_filter, Finset.mem_univ, true_and]
          have hzM := hout z hz.2
          refine ⟨hzM, fun hzr => hyr (hedge ⟨z, hzM⟩ ⟨y, hyM⟩ hzr hz.1.symm ?_ ?_), hzv⟩
          · by_cases hzu : z = u
            · exact Or.inr hyv
            · exact Or.inl hzu
          · exact Or.inl hzv
    have h1 := Finset.card_le_card hsub
    have hyn : y ∉ G.neighborFinset y \ Sf := by simp
    rw [Finset.card_insert_of_notMem hyn] at h1
    have h2 := Finset.card_insert_le v As
    have := hbig y
    omega
  obtain ⟨A0, hA0, hA0c⟩ := Finset.exists_subset_card_eq hAcard
  obtain ⟨B0, hB0, hB0c⟩ := Finset.exists_subset_card_eq hBcard
  exact ⟨A0, B0, hA0c, hB0c, fun a ha => hAprop a (hA0 ha), fun b hb => hBprop b (hB0 hb),
    fun a ha b hb => hABprop a (hA0 ha) b (hB0 hb)⟩
