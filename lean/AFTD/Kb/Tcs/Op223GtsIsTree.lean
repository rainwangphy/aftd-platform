import AFTD.Prelude
import AFTD.Kb.Tcs.IsGeneralizedTreeShift
import AFTD.Kb.Tcs.GtsGraph
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# op223_gts_is_tree

Topic: graphs   Node: f3c2610bfc78

Provenance: formalization of a published result. Source: arXiv:2610.17078 Section 2

For any simple graphs T and T' on a type V, if T' is obtained from T by a generalized tree shift, then T' is a tree.
-/

lemma op223_gts_is_tree_sym2_mem {V : Type*} {x : V} (P : V → Prop) (a b : V) :
    s(a, b) ∈ {e : Sym2 V | ∃ z, e = s(x, z) ∧ P z} ↔ (a = x ∧ P b) ∨ (b = x ∧ P a) := by
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, he, hP⟩
    rw [Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, hP⟩
    · exact Or.inr ⟨rfl, hP⟩
  · rintro (⟨rfl, hP⟩ | ⟨rfl, hP⟩)
    · exact ⟨b, rfl, hP⟩
    · exact ⟨a, Sym2.eq_swap, hP⟩

/-- A generalized tree shift applied to a tree yields another tree. -/
theorem op223_gts_is_tree {V : Type*} (T T' : SimpleGraph V)
    (h : is_generalized_tree_shift T T') :
    T'.IsTree := by
  classical
  obtain ⟨hT, u, v, p, hp, huv, hdeg, hTeq⟩ := h
  set w : V := p.penultimate with hw
  set A : Set V := {z | T.Adj v z ∧ z ≠ w} with hA
  set F : Set (Sym2 V) := {e | ∃ z, e = s(v, z) ∧ T.Adj v z ∧ z ≠ w} with hF
  set N : Set (Sym2 V) := {e | ∃ z, e = s(u, z) ∧ T.Adj v z ∧ z ≠ w} with hN
  have hT'eq : T' = T.deleteEdges F ⊔ SimpleGraph.fromEdgeSet N := hTeq
  have hTacyc : T.IsAcyclic := hT.isAcyclic
  have huA : u ∉ A := by
    simp only [hA, Set.mem_ofPred_eq]
    rintro ⟨hadj, hne⟩
    exact hne (hTacyc.eq_penultimate_of_adj_end hp hadj p.start_mem_support)
  have hvA : v ∉ A := by
    simp only [hA, Set.mem_ofPred_eq]
    exact fun h => SimpleGraph.irrefl T h.1
  have hFs : ∀ a b : V, s(a,b) ∈ F ↔ (a = v ∧ b ∈ A) ∨ (b = v ∧ a ∈ A) := by
    intro a b
    rw [hF, hA]
    exact op223_gts_is_tree_sym2_mem (fun z => T.Adj v z ∧ z ≠ w) a b
  have hNs : ∀ a b : V, s(a,b) ∈ N ↔ (a = u ∧ b ∈ A) ∨ (b = u ∧ a ∈ A) := by
    intro a b
    rw [hN, hA]
    exact op223_gts_is_tree_sym2_mem (fun z => T.Adj v z ∧ z ≠ w) a b
  have hFN : ∀ a b : V, s(a,b) ∈ F → s(a,b) ∈ N → False := by
    intro a b hf hn
    rw [hFs] at hf
    rw [hNs] at hn
    rcases hf with ⟨rfl, hbA⟩ | ⟨rfl, haA⟩
    · rcases hn with ⟨ha, -⟩ | ⟨hb, -⟩
      · exact huv ha.symm
      · rw [hb] at hbA; exact huA hbA
    · rcases hn with ⟨ha, -⟩ | ⟨hb, -⟩
      · rw [ha] at haA; exact huA haA
      · exact huv hb.symm
  have hFT' : ∀ a b : V, s(a,b) ∈ F → s(a,b) ∉ T'.edgeSet := by
    intro a b habF habT'
    rw [hT'eq, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_deleteEdges,
      SimpleGraph.edgeSet_fromEdgeSet] at habT'
    rcases habT' with ⟨-, h2⟩ | ⟨h2, -⟩
    · exact h2 habF
    · exact hFN a b habF h2
  have hT'adj : ∀ a b : V, T'.Adj a b ↔ (T.Adj a b ∧ s(a,b) ∉ F) ∨ s(a,b) ∈ N := by
    intro a b
    rw [hT'eq, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr h1
    · rintro (⟨h1, h2⟩ | h1)
      · exact Or.inl ⟨h1, h2⟩
      · have hd : a ≠ b := by
          rintro rfl
          rw [hNs] at h1
          rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1] at h2; exact huA h2
          · rw [h1] at h2; exact huA h2
        exact Or.inr ⟨h1, hd⟩
  have hpF : ∀ e ∈ p.edges, e ∉ F := by
    intro e he heF
    rw [hF] at heF
    obtain ⟨z, rfl, hzv, hzw⟩ := heF
    exact hzw (hTacyc.eq_penultimate_of_adj_end hp hzv
      (SimpleGraph.Walk.snd_mem_support_of_mem_edges p he))
  have hpT' : ∀ e ∈ p.edges, e ∈ T'.edgeSet := by
    intro e he
    rw [hT'eq, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_deleteEdges,
      SimpleGraph.edgeSet_fromEdgeSet]
    exact Or.inl ⟨p.edges_subset_edgeSet he, hpF e he⟩
  have hpwalk : T'.Walk u v := p.transfer T' hpT'
  have hpReach : T'.Reachable v u := ⟨hpwalk.reverse⟩
  have hstep : ∀ a b : V, T.Adj a b → T'.Reachable a b := by
    intro a b hab
    by_cases hFab : s(a,b) ∈ F
    · rw [hFs] at hFab
      rcases hFab with ⟨rfl, hbA⟩ | ⟨rfl, haA⟩
      · exact hpReach.trans ((hT'adj u b).mpr (Or.inr ((hNs u b).mpr (Or.inl ⟨rfl, hbA⟩)))).reachable
      · exact (hpReach.trans ((hT'adj u a).mpr (Or.inr ((hNs u a).mpr (Or.inl ⟨rfl, haA⟩)))).reachable).symm
    · exact ((hT'adj a b).mpr (Or.inl ⟨hab, hFab⟩)).reachable
  have hpre : T'.Preconnected := by
    intro a b
    have hab : T.Reachable a b := hT.connected.preconnected a b
    rw [SimpleGraph.reachable_iff_reflTransGen] at hab
    induction hab with
    | refl => exact SimpleGraph.Reachable.rfl
    | tail _ hbc ih => exact ih.trans (hstep _ _ hbc)
  have hconn : T'.Connected := (SimpleGraph.connected_iff T').mpr ⟨hpre, hT.connected.nonempty⟩
  have hbridgeA : ∀ z ∈ A, ¬ (T.deleteEdges {s(v,z)}).Reachable v z := by
    intro z hz
    have hb : T.IsBridge s(v, z) := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hTacyc hz.1
    exact SimpleGraph.isBridge_iff.mp hb
  have hptrans : ∀ z ∈ A, (T.deleteEdges {s(v,z)}).Walk u v := by
    intro z hz
    refine p.transfer _ (fun e he => ?_)
    rw [SimpleGraph.edgeSet_deleteEdges]
    refine ⟨p.edges_subset_edgeSet he, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hh
    exact hpF e he (hh ▸ ((hFs v z).mpr (Or.inl ⟨rfl, hz⟩)))
  have hFs' : ∀ z : V, s(v,z) ∈ F ↔ z ∈ A := by
    intro z
    rw [hFs]
    exact ⟨fun h => h.elim (fun h => h.2) (fun h => absurd h.2 hvA), fun h => Or.inl ⟨rfl, h⟩⟩
  have hNleft : ∀ z : V, s(u,z) ∈ N ↔ z ∈ A := by
    intro z
    rw [hNs]
    exact ⟨fun h => h.elim (fun h => h.2) (fun h => absurd h.2 huA), fun h => Or.inl ⟨rfl, h⟩⟩
  have KL2 : ∀ z₁ z₂ : V, z₁ ∈ A → z₂ ∈ A → z₁ ≠ z₂ →
      ∀ W : T.Walk z₁ z₂, s(v,z₁) ∈ W.edges := by
    intro z₁ z₂ h1 h2 hne W
    by_contra hcon
    apply hbridgeA z₁ h1
    have hW1 : (T.deleteEdges {s(v,z₁)}).Reachable z₁ z₂ := by
      rw [SimpleGraph.reachable_deleteEdges_iff_exists_walk]
      exact ⟨W, hcon⟩
    have hW2 : (T.deleteEdges {s(v,z₁)}).Reachable z₂ v := by
      have hadj : (T.deleteEdges {s(v,z₁)}).Adj z₂ v := by
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨h2.1.symm, ?_⟩
        simp only [Set.mem_singleton_iff]
        intro hh
        rw [Sym2.eq_iff] at hh
        rcases hh with ⟨-, h'⟩ | ⟨h', -⟩
        · exact SimpleGraph.irrefl T (h' ▸ h1.1)
        · exact hne h'.symm
      exact hadj.reachable
    exact (hW1.trans hW2).symm
  have KL3 : ∀ z y : V, z ∈ A → T.Adj y u → s(y,u) ∉ F →
      ∀ W : T.Walk z y, s(v,z) ∈ W.edges := by
    intro z y hz hadj hnotF W
    by_contra hcon
    apply hbridgeA z hz
    have hW1 : (T.deleteEdges {s(v,z)}).Reachable z y := by
      rw [SimpleGraph.reachable_deleteEdges_iff_exists_walk]
      exact ⟨W, hcon⟩
    have hW2 : (T.deleteEdges {s(v,z)}).Reachable y v := by
      have hadj' : (T.deleteEdges {s(v,z)}).Adj y u := by
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨hadj, ?_⟩
        simp only [Set.mem_singleton_iff]
        intro hh
        exact hnotF (hh ▸ ((hFs v z).mpr (Or.inl ⟨rfl, hz⟩)))
      exact hadj'.reachable.trans ⟨hptrans z hz⟩
    exact (hW1.trans hW2).symm
  refine ⟨hconn, ?_⟩
  intro x₀ c hc
  have hedgeT' : ∀ {a b : V} (W : T'.Walk a b) ⦃e : Sym2 V⦄, e ∈ W.edges →
      e ∈ T.edgeSet ∨ e ∈ N := by
    intro a b W e he
    have h1 : e ∈ T'.edgeSet := W.edges_subset_edgeSet he
    rw [hT'eq, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_deleteEdges,
      SimpleGraph.edgeSet_fromEdgeSet] at h1
    rcases h1 with ⟨hh, -⟩ | ⟨hh, -⟩
    · exact Or.inl hh
    · exact Or.inr hh
  by_cases hnew : ∃ e ∈ c.edges, e ∈ N
  · obtain ⟨e₀, he₀, he₀N⟩ := hnew
    have husupp : u ∈ c.support := by
      rw [hN] at he₀N
      obtain ⟨z, rfl, -⟩ := he₀N
      exact SimpleGraph.Walk.fst_mem_support_of_mem_edges c he₀
    set c' : T'.Walk u u := c.rotate u husupp with hc'def
    have hc' : c'.IsCycle := hc.rotate husupp
    have hlen : 3 ≤ c'.length := hc'.isCircuit.three_le_length
    have htnn : ¬ c'.tail.Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length, SimpleGraph.Walk.length_tail]; omega
    set y : V := (c'.tail).penultimate with hy
    let M : T'.Walk c'.snd y := (c'.tail).dropLast
    have hMsupp : M.support = (c'.tail.support).dropLast :=
      SimpleGraph.Walk.support_dropLast htnn
    have htnod : (c'.tail.support).Nodup := by
      rw [SimpleGraph.Walk.support_tail_of_not_nil c' hc'.not_nil]
      exact hc'.support_nodup
    have huM : u ∉ M.support := by
      rw [hMsupp]
      have hl : (c'.tail.support).dropLast ++ [u] = c'.tail.support :=
        SimpleGraph.Walk.dropLast_support_concat c'.tail
      have hnod : ((c'.tail.support).dropLast ++ [u]).Nodup := by rw [hl]; exact htnod
      intro hmem
      exact (List.nodup_append.mp hnod).2.2 u hmem u (by simp) rfl
    have hMT : ∀ e ∈ M.edges, e ∈ T.edgeSet := by
      intro e he
      rcases hedgeT' M he with hh | hh
      · exact hh
      · rw [hN] at hh
        obtain ⟨z, rfl, -⟩ := hh
        exact absurd (SimpleGraph.Walk.fst_mem_support_of_mem_edges M he) huM
    have hMF : ∀ a b : V, s(a,b) ∈ M.edges → s(a,b) ∉ F := by
      intro a b he
      exact fun hF' => hFT' a b hF' (M.edges_subset_edgeSet he)
    have hcedges1 : c'.edges = s(u, c'.snd) :: c'.tail.edges := by
      nth_rewrite 1 [← SimpleGraph.Walk.cons_tail_eq c' hc'.not_nil]
      simp [SimpleGraph.Walk.edges_cons]
    have hcedges2 : c'.tail.edges = M.edges ++ [s(y, u)] := by
      conv_lhs => rw [← SimpleGraph.Walk.concat_dropLast (p := c'.tail) (SimpleGraph.Walk.adj_penultimate htnn)]
      rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append]
    have hcedges : c'.edges = s(u, c'.snd) :: (M.edges ++ [s(y, u)]) := by
      rw [hcedges1, hcedges2]
    have hyN : s(y, u) ∈ N ↔ y ∈ A := by
      rw [hNs]
      exact ⟨fun h => h.elim (fun h => h.1 ▸ h.2) (fun h => h.2), fun h => Or.inr ⟨rfl, h⟩⟩
    have hmem_last : s(y, u) ∈ c'.edges := by
      rw [hcedges]
      exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    have hmem_first : s(u, c'.snd) ∈ c'.edges := by
      rw [hcedges]; exact List.mem_cons_self ..
    by_cases hxA : c'.snd ∈ A
    · by_cases hyA : y ∈ A
      · have hxy : c'.snd ≠ y := by
          intro hxy'
          have hnod := hc'.isCircuit.isTrail.edges_nodup
          rw [hcedges] at hnod
          rw [List.nodup_cons] at hnod
          exact hnod.1 (List.mem_append_right _ (List.mem_singleton.mpr (by rw [hxy']; exact Sym2.eq_swap.symm)))
        have hkl := KL2 c'.snd y hxA hyA hxy (M.transfer T hMT)
        rw [SimpleGraph.Walk.edges_transfer] at hkl
        exact (hMF v c'.snd hkl) ((hFs' c'.snd).mpr hxA)
      · have hyT : T.Adj y u := by
          rcases hedgeT' c' hmem_last with hh | hh
          · rwa [SimpleGraph.mem_edgeSet] at hh
          · exact absurd (hyN.mp hh) hyA
        have hyF : s(y, u) ∉ F := fun hh => hFT' y u hh (c'.edges_subset_edgeSet hmem_last)
        have hkl := KL3 c'.snd y hxA hyT hyF (M.transfer T hMT)
        rw [SimpleGraph.Walk.edges_transfer] at hkl
        exact (hMF v c'.snd hkl) ((hFs' c'.snd).mpr hxA)
    · by_cases hyA : y ∈ A
      · have hxT : T.Adj u c'.snd := by
          rcases hedgeT' c' hmem_first with hh | hh
          · rwa [SimpleGraph.mem_edgeSet] at hh
          · exact absurd ((hNleft c'.snd).mp hh) hxA
        have hxF : s(c'.snd, u) ∉ F := by
          intro hh
          exact hFT' u c'.snd (by rwa [Sym2.eq_swap] at hh) (c'.edges_subset_edgeSet hmem_first)
        have hkl := KL3 y c'.snd hyA hxT.symm hxF (M.transfer T hMT).reverse
        rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse, SimpleGraph.Walk.edges_transfer] at hkl
        exact (hMF v y hkl) ((hFs' y).mpr hyA)
      · have hxT : T.Adj u c'.snd := by
          rcases hedgeT' c' hmem_first with hh | hh
          · rwa [SimpleGraph.mem_edgeSet] at hh
          · exact absurd ((hNleft c'.snd).mp hh) hxA
        have hyT : T.Adj y u := by
          rcases hedgeT' c' hmem_last with hh | hh
          · rwa [SimpleGraph.mem_edgeSet] at hh
          · exact absurd (hyN.mp hh) hyA
        have hall : ∀ e ∈ c'.edges, e ∈ T.edgeSet := by
          intro e he
          rw [hcedges] at he
          rcases List.mem_cons.mp he with rfl | he
          · exact (SimpleGraph.mem_edgeSet T).mpr hxT
          · rcases List.mem_append.mp he with he | he
            · exact hMT e he
            · rw [List.mem_singleton] at he
              exact he ▸ (SimpleGraph.mem_edgeSet T).mpr hyT
        exact hTacyc (c'.transfer T hall) (hc'.transfer hall)
  · simp only [not_exists, not_and] at hnew
    have hall : ∀ e ∈ c.edges, e ∈ T.edgeSet := fun e he => (hedgeT' c he).resolve_right (hnew e he)
    exact hTacyc (c.transfer T hall) (hc.transfer hall)
