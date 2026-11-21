import AFTD.Prelude
import AFTD.Kb.Tcs.ForcedMatchingEdgeCommonNonneighborsBelowMinDegreeIsBridge

/-!
# forced_matching_edge_common_nonneighbor_degree_bound_is_bridge

Topic: graphs   Node: 8776c9ce0510

Provenance: helper lemma. OP-1957; localized strengthening of forced_matching_edge_common_nonneighbors_below_min_degree_is_bridge for the boundary residual route.

A forced perfect-matching edge is a bridge if the number of its common nonneighbors is less than r and each common nonneighbor has degree at least r; no degree assumption is imposed on other vertices.
-/

theorem forced_matching_edge_common_nonneighbor_degree_bound_is_bridge
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (u v : V)
    (hdeg : ∀ x, (Gᶜ).Adj u x → (Gᶜ).Adj v x → r ≤ G.degree x) (huv : G.Adj u v)
    (hP : ∃ P : G.Subgraph, P.IsPerfectMatching ∧ P.Adj u v)
    (hforced : ¬ ∃ P : (G.deleteEdges {s(u,v)}).Subgraph, P.IsPerfectMatching)
    (hco : ({w | (Gᶜ).Adj u w ∧ (Gᶜ).Adj v w} : Set V).ncard < r) :
    ¬ (G.deleteEdges {s(u,v)}).Reachable u v := open SimpleGraph in by
  classical
  intro hreach
  obtain ⟨P, hPm, -⟩ := hP
  have hG'adj : ∀ x y, (G.deleteEdges {s(u,v)}).Adj x y ↔ G.Adj x y ∧ s(x, y) ≠ s(u, v) := by
    intro x y; simp [SimpleGraph.deleteEdges_adj]
  have hsym : ∀ x y : V, s(x, y) = s(u, v) → (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
    intro x y h; simpa [Sym2.eq_iff] using h
  have heven : Even (Nat.card V) := by rw [Nat.card_eq_fintype_card]; exact hPm.even_card
  obtain ⟨S, hS⟩ := exists_isTutteViolator (G := G.deleteEdges {s(u,v)})
    (fun M hM => hforced ⟨M, hM⟩) heven
  -- u and v are not in S
  have hnotS : ¬ (u ∈ S ∨ v ∈ S) := by
    intro huvS
    apply not_isTutteViolator_of_isPerfectMatching hPm S
    unfold IsTutteViolator at hS ⊢
    have heq : ((⊤ : G.Subgraph).deleteVerts S).coe =
        ((⊤ : (G.deleteEdges {s(u,v)}).Subgraph).deleteVerts S).coe := by
      ext x y
      change (_ ∧ _ ∧ G.Adj x.1 y.1) ↔ (_ ∧ _ ∧ (G.deleteEdges {s(u,v)}).Adj x.1 y.1)
      constructor
      · rintro ⟨hx, hy, hxy⟩
        refine ⟨hx, hy, (hG'adj _ _).mpr ⟨hxy, fun he => ?_⟩⟩
        have hx' : x.1 ∉ S := hx.2
        have hy' : y.1 ∉ S := hy.2
        rcases hsym _ _ he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rcases huvS with h | h
        · exact hx' (h1 ▸ h)
        · exact hy' (h2 ▸ h)
        · exact hy' (h2 ▸ h)
        · exact hx' (h1 ▸ h)
      · rintro ⟨hx, hy, hxy⟩
        exact ⟨hx, hy, ((hG'adj _ _).mp hxy).1⟩
    rw [heq]
    exact hS
  have huS : u ∉ S := fun h => hnotS (Or.inl h)
  have hvS : v ∉ S := fun h => hnotS (Or.inr h)
  set G' := G.deleteEdges {s(u,v)} with hG'def
  let W : Set V := ((⊤ : G'.Subgraph).deleteVerts S).verts
  let H := ((⊤ : G'.Subgraph).deleteVerts S).coe
  have hHadj : ∀ x y : W, H.Adj x y ↔ G'.Adj x.1 y.1 := by
    intro x y
    change (_ ∧ _ ∧ G'.Adj x.1 y.1) ↔ _
    exact ⟨fun h => h.2.2, fun h => ⟨x.2, y.2, h⟩⟩
  have hW : ∀ x : V, x ∈ W ↔ x ∉ S := by
    intro x
    change x ∈ (Set.univ \ S) ↔ _
    simp
  let uW : W := ⟨u, (hW u).2 huS⟩
  let vW : W := ⟨v, (hW v).2 hvS⟩
  let cu := H.connectedComponentMk uW
  let cv := H.connectedComponentMk vW
  have hS' : S.ncard < H.oddComponents.ncard := hS
  -- parity: at least |S| + 2 odd components
  have hpar := odd_ncard_oddComponents H
  have hcardW : Nat.card W = Fintype.card V - S.ncard := by
    rw [Nat.card_coe_set_eq]
    change (Set.univ \ S).ncard = _
    rw [Set.ncard_diff (Set.subset_univ S), Set.ncard_univ, Nat.card_eq_fintype_card]
  have hSle : S.ncard ≤ Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ S)
  have hev : Fintype.card V % 2 = 0 := by
    rw [← Nat.card_eq_fintype_card]; exact Nat.even_iff.mp heven
  rw [hcardW, Nat.odd_iff, Nat.odd_iff] at hpar
  have hN : S.ncard + 2 ≤ H.oddComponents.ncard := by
    by_contra hlt
    have h1 : H.oddComponents.ncard = S.ncard + 1 := by omega
    rw [h1] at hpar
    omega
  -- the odd components avoiding u and v
  let A := H.oddComponents \ {cu, cv}
  have hAle : H.oddComponents.ncard ≤ A.ncard + ({cu, cv} : Set H.ConnectedComponent).ncard := by
    calc H.oddComponents.ncard ≤ (A ∪ {cu, cv}).ncard := by
          apply Set.ncard_le_ncard _ (Set.toFinite _)
          intro c hc
          by_cases h : c ∈ ({cu, cv} : Set H.ConnectedComponent)
          · exact Or.inr h
          · exact Or.inl ⟨hc, h⟩
      _ ≤ A.ncard + ({cu, cv} : Set H.ConnectedComponent).ncard := Set.ncard_union_le _ _
  have hpair : ({cu, cv} : Set H.ConnectedComponent).ncard ≤ 2 := by
    calc ({cu, cv} : Set H.ConnectedComponent).ncard ≤ ({cv} : Set H.ConnectedComponent).ncard + 1 :=
          Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have hAs : S.ncard ≤ A.ncard := by omega
  have hApos : 0 < A.ncard := by
    rcases Nat.eq_zero_or_pos S.ncard with h0 | hpos
    · have hS0 : S = ∅ := (Set.ncard_eq_zero (Set.toFinite S)).mp h0
      have hcucv : cu = cv := by
        let φ : G' →g H :=
          { toFun := fun x => ⟨x, (hW x).2 (by rw [hS0]; exact Set.notMem_empty x)⟩
            map_rel' := fun {x y} h => (hHadj _ _).2 h }
        have hr : H.Reachable (φ u) (φ v) := hreach.map φ
        exact ConnectedComponent.eq.mpr hr
      have h1 : ({cu, cv} : Set H.ConnectedComponent).ncard = 1 := by
        rw [hcucv, Set.pair_eq_singleton, Set.ncard_singleton]
      omega
    · omega
  obtain ⟨D, hDA⟩ := Set.nonempty_of_ncard_ne_zero (Nat.pos_iff_ne_zero.mp hApos)
  -- vertices of components other than cu, cv
  have hfar : ∀ c : H.ConnectedComponent, c ≠ cu → c ≠ cv → ∀ x : W, x ∈ c.supp →
      x.1 ≠ u ∧ x.1 ≠ v ∧ ¬ G.Adj x.1 u ∧ ¬ G.Adj x.1 v := by
    intro c hcu hcv x hx
    rw [ConnectedComponent.mem_supp_iff] at hx
    have hxu : x.1 ≠ u := by
      intro h
      apply hcu
      rw [← hx]
      exact congrArg H.connectedComponentMk (Subtype.ext h)
    have hxv : x.1 ≠ v := by
      intro h
      apply hcv
      rw [← hx]
      exact congrArg H.connectedComponentMk (Subtype.ext h)
    refine ⟨hxu, hxv, ?_, ?_⟩
    · intro hadj
      apply hcu
      rw [← hx]
      apply ConnectedComponent.eq.mpr
      apply SimpleGraph.Adj.reachable
      rw [hHadj]
      refine (hG'adj _ _).mpr ⟨hadj, fun he => ?_⟩
      rcases hsym _ _ he with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hxu h1
      · exact hxv h1
    · intro hadj
      apply hcv
      rw [← hx]
      apply ConnectedComponent.eq.mpr
      apply SimpleGraph.Adj.reachable
      rw [hHadj]
      refine (hG'adj _ _).mpr ⟨hadj, fun he => ?_⟩
      rcases hsym _ _ he with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hxu h1
      · exact hxv h1
  have hDodd : D ∈ H.oddComponents := hDA.1
  have hDne : D ≠ cu ∧ D ≠ cv := by
    have h := hDA.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
    exact h
  -- the common non-neighbour set
  let C : Set V := {w | (Gᶜ).Adj u w ∧ (Gᶜ).Adj v w}
  have hinC : ∀ c : H.ConnectedComponent, c ≠ cu → c ≠ cv → ∀ x : W, x ∈ c.supp → x.1 ∈ C := by
    intro c hcu hcv x hx
    obtain ⟨hxu, hxv, hau, hav⟩ := hfar c hcu hcv x hx
    exact ⟨(compl_adj G u x.1).2 ⟨Ne.symm hxu, fun h => hau h.symm⟩,
      (compl_adj G v x.1).2 ⟨Ne.symm hxv, fun h => hav h.symm⟩⟩
  -- a representative of every component
  have hrep : ∀ c : H.ConnectedComponent, ∃ x : W, x ∈ c.supp := fun c => c.nonempty_supp
  choose rep hrep using hrep
  let Dset : Set V := Subtype.val '' D.supp
  let R : Set V := (fun c => (rep c).1) '' (A \ {D})
  have hRinj : Set.InjOn (fun c => (rep c).1) (A \ {D}) := by
    intro c _ c' _ h
    have h1 := hrep c
    have h2 := hrep c'
    rw [ConnectedComponent.mem_supp_iff] at h1 h2
    have : rep c = rep c' := Subtype.ext h
    rw [← h1, ← h2, this]
  have hdisj : Disjoint Dset R := by
    rw [Set.disjoint_left]
    rintro z ⟨x, hx, rfl⟩ ⟨c, hc, hcz⟩
    have h1 := hrep c
    have hx' := hx
    rw [ConnectedComponent.mem_supp_iff] at h1 hx'
    have : rep c = x := Subtype.ext hcz
    apply hc.2
    rw [Set.mem_singleton_iff, ← h1, this, hx']
  have hsubC : Dset ∪ R ⊆ C := by
    rintro z (⟨x, hx, rfl⟩ | ⟨c, hc, rfl⟩)
    · exact hinC D hDne.1 hDne.2 x hx
    · have hcA := hc.1
      have hcne := hcA.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcne
      exact hinC c hcne.1 hcne.2 (rep c) (hrep c)
  have hCcard : Dset.ncard + (A.ncard - 1) ≤ C.ncard := by
    have h1 := Set.ncard_le_ncard hsubC (Set.toFinite C)
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
      Set.ncard_image_of_injOn hRinj, Set.ncard_sdiff_singleton_of_mem hDA] at h1
    exact h1
  -- degree bound inside D
  obtain ⟨x, hxD⟩ := D.nonempty_supp
  have hnb : G.neighborSet x.1 ⊆ (Dset \ {x.1}) ∪ S := by
    intro y hy
    rw [SimpleGraph.mem_neighborSet] at hy
    by_cases hyS : y ∈ S
    · exact Or.inr hyS
    · left
      obtain ⟨hxu, hxv, -, -⟩ := hfar D hDne.1 hDne.2 x hxD
      refine ⟨⟨⟨y, (hW y).2 hyS⟩, ?_, rfl⟩, ?_⟩
      · rw [ConnectedComponent.mem_supp_iff] at hxD ⊢
        rw [← hxD]
        apply ConnectedComponent.eq.mpr
        apply SimpleGraph.Adj.reachable
        rw [hHadj]
        refine (hG'adj _ _).mpr ⟨hy.symm, fun he => ?_⟩
        rcases hsym _ _ he with ⟨-, h1⟩ | ⟨-, h1⟩
        · exact hxv h1
        · exact hxu h1
      · rw [Set.mem_singleton_iff]
        exact fun h => hy.ne h.symm
  have hdegx : G.degree x.1 ≤ (Dset.ncard - 1) + S.ncard := by
    have h1 := Set.ncard_le_ncard hnb (Set.toFinite _)
    have h2 := Set.ncard_union_le (Dset \ {x.1}) S
    have hxmem : x.1 ∈ Dset := ⟨x, hxD, rfl⟩
    rw [Set.ncard_sdiff_singleton_of_mem hxmem] at h2
    have h3 : (G.neighborSet x.1).ncard = G.degree x.1 := by
      rw [Set.ncard_eq_toFinset_card', ← SimpleGraph.card_neighborFinset_eq_degree,
        SimpleGraph.neighborFinset_eq_filter]
      simp
    omega
  have hDpos : 0 < Dset.ncard := Set.ncard_pos (Set.toFinite _) |>.mpr ⟨x.1, x, hxD, rfl⟩
  have hxC := hinC D hDne.1 hDne.2 x hxD
  have := hdeg x.1 hxC.1 hxC.2
  have hco' : C.ncard < r := hco
  omega
