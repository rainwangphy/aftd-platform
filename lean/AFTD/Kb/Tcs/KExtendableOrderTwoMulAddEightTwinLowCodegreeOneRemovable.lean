import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.Op2037SubgraphFintype
import AFTD.Kb.Tcs.ForcedMatchingEdgeCommonNonneighborsBelowMinDegreeIsBridge
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# k_extendable_order_two_mul_add_eight_twin_low_codegree_one_removable

Topic: graphs   Node: 1f8f400c937b

Provenance: helper lemma. OP-1957: saturated twin-pair degree-budget bottleneck; experiment 34622 checks the final finite obstruction.

For a k-extendable graph on 2k+8 vertices with k at least four and minimum degree at least 2k+2, let a,b be degree-five complement twins. Of any two distinct graph edges from a to vertices other than b, each with complement codegree at most one, at least one can be deleted while preserving k-extendability.
-/

open SimpleGraph in
theorem in1069_transport {V : Type*} (G : SimpleGraph V) (u v : V)
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
theorem in1069_verts_bound {n k : ℕ} {H : SimpleGraph (Fin n)} (M : H.Subgraph) (hM : M.IsMatching)
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

open SimpleGraph in
theorem in1069_verts_card {n k : ℕ} {H : SimpleGraph (Fin n)} (M : H.Subgraph) (hM : M.IsMatching)
    (hMk : M.edgeSet.ncard = k) :
    ∃ S : Finset (Fin n), (∀ x, x ∈ M.verts ↔ x ∈ S) ∧ S.card = 2 * k := by
  classical
  refine ⟨(M.edgeSet.toFinite.toFinset).biUnion (fun e => e.toFinset), ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨w, hw, -⟩ := hM hx
      rw [Finset.mem_biUnion]
      exact ⟨s(x, w), by simpa using hw, by simp⟩
    · intro hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨e, he, hxe⟩ := hx
      rw [Set.Finite.mem_toFinset] at he
      rw [Sym2.mem_toFinset] at hxe
      exact M.mem_verts_of_mem_edge he hxe
  · rw [Finset.card_biUnion]
    · have h2 : ∀ e ∈ M.edgeSet.toFinite.toFinset, e.toFinset.card = 2 := by
        intro e he
        rw [Set.Finite.mem_toFinset] at he
        rw [Sym2.card_toFinset]
        have : ¬ e.IsDiag := H.not_isDiag_of_mem_edgeSet (M.edgeSet_subset he)
        simp [this]
      rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul,
        ← Set.ncard_eq_toFinset_card M.edgeSet M.edgeSet.toFinite, hMk]
      ring
    · intro e he e' he' hne
      rw [Function.onFun, Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_coe, Set.Finite.mem_toFinset] at he he'
      rw [Sym2.mem_toFinset] at hx hx'
      obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hx
      obtain ⟨y', rfl⟩ := Sym2.mem_iff_exists.mp hx'
      have h1 : M.Adj x y := he
      have h2 : M.Adj x y' := he'
      obtain ⟨z, -, hz⟩ := hM (M.edge_vert h1)
      exact hne (by rw [hz y h1, hz y' h2])

theorem in1069_even_of_pairing {V : Type*} [DecidableEq V] (S : Finset V) (R : V → V → Prop)
    (hsymm : ∀ x y, R x y → R y x) (hirr : ∀ x, ¬ R x x)
    (hex : ∀ x ∈ S, ∃ y ∈ S, R x y) (huniq : ∀ x y y', R x y → R x y' → y = y') :
    Even S.card := by
  classical
  let Q : SimpleGraph S :=
    { Adj := fun a b => R a.1 b.1
      symm := ⟨fun a b h => hsymm _ _ h⟩
      loopless := ⟨fun a h => hirr _ h⟩ }
  have hQ : (⊤ : Q.Subgraph).IsPerfectMatching := by
    rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
    intro x
    obtain ⟨y, hy, hxy⟩ := hex x.1 x.2
    refine ⟨⟨y, hy⟩, hxy, ?_⟩
    intro z hz
    exact Subtype.ext (huniq _ _ _ hz hxy)
  have := hQ.even_card
  rwa [Fintype.card_coe] at this


theorem in1069_bridge
    (k n r : ℕ) (hr : 2 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (huv : G.Adj u v)
    (hext0 : is_k_extendable G k) (hnot0 : ¬ is_k_extendable (G.deleteEdges {s(u,v)}) k) (hdegree : 2*k+r ≤ G.minDegree)
    (hco : (((Gᶜ).neighborFinset u).filter (fun w => (Gᶜ).Adj v w)).card < r) :
    ∃ A B : Finset (Fin n), Disjoint A B ∧ u ∈ A ∧ v ∈ B ∧
      A.card + B.card + 2 * k = n ∧ Odd A.card ∧ Odd B.card ∧
      r + 1 ≤ A.card ∧ r + 1 ≤ B.card ∧
      ∀ x ∈ A, ∀ y ∈ B, (x = u ∧ y = v) ∨ (Gᶜ).Adj x y := open SimpleGraph in by
  classical
  obtain ⟨hcard, ⟨M0, hM0, hM0k⟩, hext⟩ := hext0
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
      obtain ⟨S0, hS0, hS0c⟩ := in1069_verts_bound M0 hM0 hM0k
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
  have hnot := hnot0
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
    exact hMno (in1069_transport G u v M P hP hMP.1 (fun x y hxy => hMPadj hxy) h)
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
  obtain ⟨Sf, hSf, hSfc⟩ := in1069_verts_bound MG hMG hMGk
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
    refine lt_of_le_of_lt ?_ hco
    rw [← Set.ncard_coe_finset]
    apply Set.ncard_le_ncard_of_injOn Subtype.val
    · intro w hw
      obtain ⟨h1, h2⟩ := hw
      rw [SimpleGraph.compl_adj] at h1 h2
      rw [Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨(SimpleGraph.compl_adj G u w.1).2 ⟨fun h => h1.1 (Subtype.ext h), h1.2⟩,
        (SimpleGraph.compl_adj G v w.1).2 ⟨fun h => h2.1 (Subtype.ext h), h2.2⟩⟩
    · exact Subtype.val_injective.injOn
  have key := forced_matching_edge_common_nonneighbors_below_min_degree_is_bridge Gr r hdegGr uW vW
    huv hPGr hforcedGr hcoGr
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
  have huBs : u ∉ Bs := by simp [Bs]
  have hvAs : v ∉ As := by simp [As]
  have hmemA : ∀ x, x ∈ insert u Bs ↔ ∃ h : x ∉ M.verts, Gd.Reachable uW ⟨x, h⟩ := by
    intro x
    constructor
    · intro hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨huR, SimpleGraph.Reachable.refl _⟩
      · simp only [Bs, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        obtain ⟨h, hr, -⟩ := hx
        exact ⟨h, hr⟩
    · rintro ⟨h, hr⟩
      by_cases hxu : x = u
      · rw [hxu]; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        simp only [Bs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h, hr, hxu⟩
  have hmemB : ∀ x, x ∈ insert v As ↔ ∃ h : x ∉ M.verts, ¬ Gd.Reachable uW ⟨x, h⟩ := by
    intro x
    constructor
    · intro hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨hvR, key⟩
      · simp only [As, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        obtain ⟨h, hr, -⟩ := hx
        exact ⟨h, hr⟩
    · rintro ⟨h, hr⟩
      by_cases hxv : x = v
      · rw [hxv]; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        simp only [As, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h, hr, hxv⟩
  have hdisj : Disjoint (insert u Bs) (insert v As) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨h1, r1⟩ := (hmemA x).1 hx
    obtain ⟨h2, r2⟩ := (hmemB x).1 hx'
    exact r2 r1
  -- parity
  have hevenB : Even Bs.card := by
    apply in1069_even_of_pairing Bs (fun x y => P.Adj x y) (fun x y h => h.symm)
      (fun x h => (P.adj_sub h).ne rfl) _ (fun x y y' h h' => (hP' x).unique h h')
    intro x hx
    simp only [Bs, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hxM, hxr, hxu⟩ := hx
    obtain ⟨p, hp, -⟩ := hP' x
    have hpM := hcl x p hp hxM
    have hpr : Gd.Reachable uW ⟨p, hpM⟩ :=
      hedge ⟨x, hxM⟩ ⟨p, hpM⟩ hxr (P.adj_sub hp) (Or.inl hxu) (Or.inl (hreachv _ hxr))
    have hpu : p ≠ u := by
      rintro rfl
      exact hreachv _ hxr ((hP' p).unique hp.symm hPuv)
    refine ⟨p, ?_, hp⟩
    simp only [Bs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hpM, hpr, hpu⟩
  have hevenA : Even As.card := by
    apply in1069_even_of_pairing As (fun x y => P.Adj x y) (fun x y h => h.symm)
      (fun x h => (P.adj_sub h).ne rfl) _ (fun x y y' h h' => (hP' x).unique h h')
    intro x hx
    simp only [As, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hxM, hxr, hxv⟩ := hx
    have hxu : x ≠ u := by
      rintro rfl
      exact hxr (SimpleGraph.Reachable.refl _)
    obtain ⟨p, hp, -⟩ := hP' x
    have hpM := hcl x p hp hxM
    have hpr : ¬ Gd.Reachable uW ⟨p, hpM⟩ := by
      intro hpr
      exact hxr (hedge ⟨p, hpM⟩ ⟨x, hxM⟩ hpr (P.adj_sub hp.symm) (Or.inr hxv) (Or.inr hxu))
    have hpv : p ≠ v := by
      rintro rfl
      exact hxu ((hP' p).unique hp.symm hPuv.symm)
    refine ⟨p, ?_, hp⟩
    simp only [As, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hpM, hpr, hpv⟩
  -- total size
  obtain ⟨S, hS, hSc⟩ := in1069_verts_card M hM hMk
  have hunion : insert u Bs ∪ insert v As = Sᶜ := by
    ext x
    rw [Finset.mem_union, hmemA, hmemB, Finset.mem_compl, ← hS]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      by_cases hr : Gd.Reachable uW ⟨x, h⟩
      · exact Or.inl ⟨h, hr⟩
      · exact Or.inr ⟨h, hr⟩
  have hcardU := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_compl, Fintype.card_fin] at hcardU
  have hSle : S.card ≤ n := by
    have := Finset.card_le_univ S
    rwa [Fintype.card_fin] at this
  have hcA := Finset.card_insert_of_notMem huBs
  have hcB := Finset.card_insert_of_notMem hvAs
  refine ⟨insert u Bs, insert v As, hdisj, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _,
    by omega, by rw [hcA]; exact hevenB.add_one, by rw [hcB]; exact hevenA.add_one,
    by omega, by omega, ?_⟩
  intro x hx y hy
  by_cases hxy : x = u ∧ y = v
  · exact Or.inl hxy
  · right
    obtain ⟨hxM, hxr⟩ := (hmemA x).1 hx
    obtain ⟨hyM, hyr⟩ := (hmemB y).1 hy
    refine (SimpleGraph.compl_adj G x y).2 ⟨?_, ?_⟩
    · rintro rfl
      exact hyr hxr
    · intro hadj
      exact hyr (hedge ⟨x, hxM⟩ ⟨y, hyM⟩ hxr hadj (not_and_or.mp hxy) (Or.inl (hreachv _ hxr)))

theorem k_extendable_order_two_mul_add_eight_twin_low_codegree_one_removable
    (k : ℕ) (hk : 4 ≤ k) (G : SimpleGraph (Fin (2*k+8))) [DecidableRel G.Adj]
    (hext : is_k_extendable G k) (hdegree : 2*k+2 ≤ G.minDegree)
    (a b v w : Fin (2*k+8)) (hab : a ≠ b) (htdeg : (Gᶜ).degree a = 5)
    (htwin : ∀ x, (Gᶜ).Adj a x ↔ (Gᶜ).Adj b x)
    (hav : G.Adj a v) (haw : G.Adj a w) (hvb : v ≠ b) (hwb : w ≠ b) (hvw : v ≠ w)
    (hcv : ({x | (Gᶜ).Adj a x ∧ (Gᶜ).Adj v x} : Set (Fin (2*k+8))).ncard ≤ 1)
    (hcw : ({x | (Gᶜ).Adj a x ∧ (Gᶜ).Adj w x} : Set (Fin (2*k+8))).ncard ≤ 1) :
    is_k_extendable (G.deleteEdges {s(a,v)}) k ∨ is_k_extendable (G.deleteEdges {s(a,w)}) k := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnv, hnw⟩ := hcon
  have hHdeg : ∀ x, (Gᶜ).degree x ≤ 5 := by
    intro x
    have h1 := G.degree_compl x
    have h2 := G.minDegree_le_degree x
    rw [Fintype.card_fin] at h1
    omega
  set S := (Gᶜ).neighborFinset a with hS
  have hScard : S.card = 5 := by rw [hS, SimpleGraph.card_neighborFinset_eq_degree]; exact htdeg
  have hSmem : ∀ x, x ∈ S ↔ (Gᶜ).Adj a x := fun x => by rw [hS, SimpleGraph.mem_neighborFinset]
  have hnab : ¬ (Gᶜ).Adj a b := fun h => ((htwin b).1 h).ne rfl
  have hco : ∀ y, ({x | (Gᶜ).Adj a x ∧ (Gᶜ).Adj y x} : Set (Fin (2*k+8))).ncard ≤ 1 →
      (((Gᶜ).neighborFinset a).filter (fun x => (Gᶜ).Adj y x)).card < 2 := by
    intro y h
    have : ((((Gᶜ).neighborFinset a).filter (fun x => (Gᶜ).Adj y x) : Finset (Fin (2*k+8))) :
        Set (Fin (2*k+8))) = {x | (Gᶜ).Adj a x ∧ (Gᶜ).Adj y x} := by
      ext x; simp
    rw [← Set.ncard_coe_finset, this]
    omega
  have key : ∀ y, G.Adj a y → y ≠ b → ¬ is_k_extendable (G.deleteEdges {s(a,y)}) k →
      ({x | (Gᶜ).Adj a x ∧ (Gᶜ).Adj y x} : Set (Fin (2*k+8))).ncard ≤ 1 →
      ∃ P : Finset (Fin (2*k+8)), P.card = 2 ∧ ∀ p ∈ P, p ≠ a ∧ p ≠ b ∧
        (Gᶜ).neighborFinset p \ S = {y} ∧ ((Gᶜ).neighborFinset p ∩ S).card = 4 := by
    intro y hay hyb hny hcy
    obtain ⟨A, B, hAB, haA, hyB, hcard, ho1, ho2, hlA, hlB, hcross⟩ :=
      in1069_bridge k (2*k+8) 2 le_rfl G a y hay hext hny hdegree (hco y hcy)
    have hyS : y ∉ S := by
      rw [hSmem, SimpleGraph.compl_adj]
      exact fun h => h.2 hay
    have hbA : b ∉ A := by
      intro hbA
      have h := (hcross b hbA y hyB).resolve_left (fun h => hab h.1.symm)
      exact hyS ((hSmem y).2 ((htwin y).2 h))
    have hbB : b ∉ B := by
      intro hbB
      rcases hcross a haA b hbB with ⟨-, h⟩ | h
      · exact hyb h.symm
      · exact hnab h
    have hA3 : A.card = 3 := by
      obtain ⟨m1, hm1⟩ := ho1
      obtain ⟨m2, hm2⟩ := ho2
      by_contra hne
      have hA5 : A.card = 5 := by omega
      have hB3 : B.card = 3 := by omega
      obtain ⟨p, hp⟩ : (B.erase y).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hyB]; omega
      have hpB := Finset.mem_of_mem_erase hp
      have hpy := Finset.ne_of_mem_erase hp
      have hsub : A ⊆ (Gᶜ).neighborFinset p := fun x hx =>
        (SimpleGraph.mem_neighborFinset _ _ _).2
          ((hcross x hx p hpB).resolve_left (fun h => hpy h.2)).symm
      have heq : A = (Gᶜ).neighborFinset p := Finset.eq_of_subset_of_card_le hsub
        (by rw [SimpleGraph.card_neighborFinset_eq_degree, hA5]; exact hHdeg p)
      have hpa : (Gᶜ).Adj a p := (hcross a haA p hpB).resolve_left (fun h => hpy h.2)
      have hbp : (Gᶜ).Adj b p := (htwin p).1 hpa
      apply hbA
      rw [heq, SimpleGraph.mem_neighborFinset]
      exact hbp.symm
    have hB5 : B.card = 5 := by omega
    refine ⟨A.erase a, by rw [Finset.card_erase_of_mem haA, hA3], ?_⟩
    intro p hp
    have hpA := Finset.mem_of_mem_erase hp
    have hpa := Finset.ne_of_mem_erase hp
    have hsub : B ⊆ (Gᶜ).neighborFinset p := fun x hx =>
      (SimpleGraph.mem_neighborFinset _ _ _).2 ((hcross p hpA x hx).resolve_left (fun h => hpa h.1))
    have heq : B = (Gᶜ).neighborFinset p := Finset.eq_of_subset_of_card_le hsub
      (by rw [SimpleGraph.card_neighborFinset_eq_degree, hB5]; exact hHdeg p)
    have hBS : ∀ x ∈ B, x ≠ y → x ∈ S := fun x hx hxy =>
      (hSmem x).2 ((hcross a haA x hx).resolve_left (fun h => hxy h.2))
    refine ⟨hpa, fun h => hbA (h ▸ hpA), ?_, ?_⟩
    · rw [← heq]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · rintro ⟨hxB, hxS⟩
        by_contra hxy
        exact hxS (hBS x hxB hxy)
      · rintro rfl
        exact ⟨hyB, hyS⟩
    · rw [← heq]
      have : B ∩ S = B.erase y := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_erase]
        constructor
        · rintro ⟨hxB, hxS⟩
          exact ⟨fun h => hyS (h ▸ hxS), hxB⟩
        · rintro ⟨hxy, hxB⟩
          exact ⟨hxB, hBS x hxB hxy⟩
      rw [this, Finset.card_erase_of_mem hyB, hB5]
  obtain ⟨P1, hP1c, hP1⟩ := key v hav hvb hnv hcv
  obtain ⟨P2, hP2c, hP2⟩ := key w haw hwb hnw hcw
  have hdisj : Disjoint P1 P2 := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    have e1 := (hP1 p h1).2.2.1
    have e2 := (hP2 p h2).2.2.1
    rw [e1] at e2
    exact hvw (Finset.singleton_inj.mp e2)
  set C := P1 ∪ P2 with hC
  have hCc : C.card = 4 := by rw [hC, Finset.card_union_of_disjoint hdisj, hP1c, hP2c]
  have hCp : ∀ p ∈ C, p ≠ a ∧ p ≠ b ∧ ((Gᶜ).neighborFinset p ∩ S).card = 4 := by
    intro p hp
    rcases Finset.mem_union.1 hp with h | h
    · exact ⟨(hP1 p h).1, (hP1 p h).2.1, (hP1 p h).2.2.2⟩
    · exact ⟨(hP2 p h).1, (hP2 p h).2.1, (hP2 p h).2.2.2⟩
  have hsum := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := C) (t := S) (r := fun p x => (Gᶜ).Adj p x)
  have hL : ∑ p ∈ C, (S.bipartiteAbove (fun p x => (Gᶜ).Adj p x) p).card = 16 := by
    rw [Finset.sum_congr rfl (g := fun _ => 4)]
    · rw [Finset.sum_const, hCc]; rfl
    · intro p hp
      rw [← (hCp p hp).2.2]
      congr 1
      ext x
      simp [Finset.bipartiteAbove, and_comm]
  have hR : ∑ x ∈ S, (C.bipartiteBelow (fun p x => (Gᶜ).Adj p x) x).card ≤ S.card • 3 := by
    apply Finset.sum_le_card_nsmul
    intro x hx
    have hax : (Gᶜ).Adj x a := ((hSmem x).1 hx).symm
    have hbx : (Gᶜ).Adj x b := ((htwin x).1 ((hSmem x).1 hx)).symm
    have hsub : C.bipartiteBelow (fun p x => (Gᶜ).Adj p x) x ⊆ (((Gᶜ).neighborFinset x).erase a).erase b := by
      intro p hp
      rw [Finset.bipartiteBelow, Finset.mem_filter] at hp
      rw [Finset.mem_erase, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
      exact ⟨(hCp p hp.1).2.1, (hCp p hp.1).1, hp.2.symm⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (by rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]; exact ⟨hab.symm, hbx⟩),
      Finset.card_erase_of_mem (by rw [SimpleGraph.mem_neighborFinset]; exact hax),
      SimpleGraph.card_neighborFinset_eq_degree] at h1
    have := hHdeg x
    omega
  rw [smul_eq_mul, hScard] at hR
  omega
