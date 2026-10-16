import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# simple_graph_is_tree_exists_superadditive_balanced_separator

Topic: combinatorics   Node: 609ba9fccdce

Provenance: formalization of a published result. Source: arXiv:2610.16703 (Piercing boxes and products of trees), Lemma 2.2. The components of T − v are written as the classes of reachability from w ≠ v in T with the edges at v deleted.

Let T be a tree on a finite vertex set V and f a nonnegative superadditive set function (f(A) + f(B) ≤ f(A ∪ B) for disjoint A, B). Then some vertex v has the property that every connected component C of T − v satisfies f(C) ≤ f(V)/2, and the values f(C) over the components sum to at most f(V).
-/

theorem tree_separator_superadditive_sum_le {V : Type*} [DecidableEq V] (f : Finset V → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hsup : ∀ A B, Disjoint A B → f A + f B ≤ f (A ∪ B))
    (𝒮 : Finset (Finset V)) (hd : (𝒮 : Set (Finset V)).PairwiseDisjoint id) :
    ∑ C ∈ 𝒮, f C ≤ f (𝒮.biUnion id) := by
  induction 𝒮 using Finset.induction_on with
  | empty => simpa using hf0 ∅
  | insert C 𝒮 hC ih =>
    rw [Finset.sum_insert hC, Finset.biUnion_insert]
    have hd' : (𝒮 : Set (Finset V)).PairwiseDisjoint id :=
      hd.subset (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)
    have hdisj : Disjoint C (𝒮.biUnion id) := by
      rw [Finset.disjoint_biUnion_right]
      intro D hD
      exact hd (by simp) (by simp [hD]) (fun h => hC (h ▸ hD))
    have := hsup C _ hdisj
    have := ih hd'
    simp only [id] at *
    linarith

theorem tree_separator_reachable_transfer {V : Type*} (T : SimpleGraph V) (u v a z : V)
    (p : (T.deleteIncidenceSet u).Walk a z)
    (ha : ∀ y, (T.deleteIncidenceSet u).Reachable a y → y ≠ v) :
    (T.deleteIncidenceSet v).Reachable a z := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b z h p ih =>
    have hb : ∀ y, (T.deleteIncidenceSet u).Reachable b y → y ≠ v :=
      fun y hy => ha y (h.reachable.trans hy)
    refine SimpleGraph.Reachable.trans ?_ (ih hb)
    apply SimpleGraph.Adj.reachable
    rw [SimpleGraph.deleteIncidenceSet_adj] at h ⊢
    exact ⟨h.1, ha _ (SimpleGraph.Reachable.refl _), hb _ (SimpleGraph.Reachable.refl _)⟩

theorem tree_separator_delete_le {V : Type*} (T : SimpleGraph V) (u v a : V)
    (ha : a = u ∨ a = v) : T.deleteIncidenceSet a ≤ T.deleteEdges {s(u, v)} := by
  intro x y h
  rw [SimpleGraph.deleteIncidenceSet_adj] at h
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨h.1, ?_⟩
  simp only [Set.mem_singleton_iff, Sym2.eq_iff]
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rcases ha with rfl | rfl <;> simp_all

theorem simple_graph_is_tree_exists_superadditive_balanced_separator {V : Type*} [Fintype V]
    [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    (f : Finset V → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hsup : ∀ A B, Disjoint A B → f A + f B ≤ f (A ∪ B)) :
    ∃ v : V,
      (∀ w, w ≠ v →
        f (Finset.univ.filter fun u => (T.deleteIncidenceSet v).Reachable w u) ≤
          f Finset.univ / 2) ∧
      ∑ C ∈ (Finset.univ.erase v).image
          (fun w => Finset.univ.filter fun u => (T.deleteIncidenceSet v).Reachable w u), f C ≤
        f Finset.univ := by
  have hmono : ∀ A B : Finset V, A ⊆ B → f A ≤ f B := by
    intro A B hAB
    have := hsup A (B \ A) Finset.disjoint_sdiff
    rw [Finset.union_sdiff_of_subset hAB] at this
    linarith [hf0 (B \ A)]
  have mem_comp : ∀ v w u, u ∈ (Finset.univ.filter fun u => (T.deleteIncidenceSet v).Reachable w u) ↔
      (T.deleteIncidenceSet v).Reachable w u := by
    intro v w u; simp
  have not_reach : ∀ v w, w ≠ v → ¬ (T.deleteIncidenceSet v).Reachable w v := by
    intro v w hw h
    obtain ⟨p⟩ := h.symm
    cases p with
    | nil => exact hw rfl
    | cons h' _ => exact (SimpleGraph.deleteIncidenceSet_adj.1 h').2.1 rfl
  have comp_eq : ∀ v w w', (T.deleteIncidenceSet v).Reachable w w' →
      (Finset.univ.filter fun u => (T.deleteIncidenceSet v).Reachable w u) =
        (Finset.univ.filter fun u => (T.deleteIncidenceSet v).Reachable w' u) := by
    intro v w w' h
    ext z
    rw [mem_comp, mem_comp]
    exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩
  have hsum : ∀ v, ∑ C ∈ (Finset.univ.erase v).image
      (fun w => Finset.univ.filter fun u => (T.deleteIncidenceSet v).Reachable w u), f C ≤
        f Finset.univ := by
    intro v
    refine (tree_separator_superadditive_sum_le f hf0 hsup _ ?_).trans
      (hmono _ _ (Finset.subset_univ _))
    intro C hC D hD hCD
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hC hD
    obtain ⟨w1, -, rfl⟩ := hC
    obtain ⟨w2, -, rfl⟩ := hD
    rw [Function.onFun, Finset.disjoint_left]
    intro z hz1 hz2
    apply hCD
    simp only [id] at hz1 hz2
    exact comp_eq v w1 w2 (((mem_comp _ _ _).1 hz1).trans ((mem_comp _ _ _).1 hz2).symm)
  by_contra hcon
  have heavy : ∀ v, ∃ w, w ≠ v ∧ f Finset.univ / 2 <
      f (Finset.univ.filter fun u => (T.deleteIncidenceSet v).Reachable w u) := by
    intro v
    by_contra h
    apply hcon
    refine ⟨v, fun w hw => ?_, hsum v⟩
    by_contra h2
    exact h ⟨w, hw, lt_of_not_ge h2⟩
  obtain ⟨v0⟩ := hT.1.nonempty
  let P := (Finset.univ : Finset (V × V)).filter fun p => p.2 ≠ p.1 ∧ f Finset.univ / 2 <
      f (Finset.univ.filter fun u => (T.deleteIncidenceSet p.1).Reachable p.2 u)
  have hPne : P.Nonempty := by
    obtain ⟨w, hw, hh⟩ := heavy v0
    exact ⟨(v0, w), by simp [P, hw, hh]⟩
  obtain ⟨⟨v, w⟩, hp, hmin⟩ := P.exists_min_image
    (fun p => (Finset.univ.filter fun u => (T.deleteIncidenceSet p.1).Reachable p.2 u).card) hPne
  simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  obtain ⟨hwv, hheavy⟩ := hp
  -- a neighbour u of v in the heavy component C
  obtain ⟨q⟩ := hT.1.preconnected w v
  obtain ⟨d, -, hd1, hd2⟩ := q.exists_boundary_dart
    (↑(Finset.univ.filter fun u => (T.deleteIncidenceSet v).Reachable w u) : Set V)
    (by rw [Finset.mem_coe, mem_comp]) (by rw [Finset.mem_coe, mem_comp]; exact not_reach v w hwv)
  rw [Finset.mem_coe, mem_comp] at hd1 hd2
  have hfst : d.fst ≠ v := fun h => not_reach v w hwv (h ▸ hd1)
  have hsnd : d.snd = v := by
    by_contra hne
    exact hd2 (hd1.trans (SimpleGraph.Adj.reachable
      (SimpleGraph.deleteIncidenceSet_adj.2 ⟨d.adj, hfst, hne⟩)))
  set u := d.fst with hu_def
  have huv : T.Adj u v := hsnd ▸ d.adj
  have hwu : (T.deleteIncidenceSet v).Reachable w u := hd1
  have hvu : v ≠ u := fun h => hfst h.symm
  -- the component of v in T - u is disjoint from C
  have hdisj : Disjoint (Finset.univ.filter fun z => (T.deleteIncidenceSet u).Reachable v z)
      (Finset.univ.filter fun z => (T.deleteIncidenceSet v).Reachable w z) := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    rw [mem_comp] at hz1 hz2
    have h1 := hz1.mono (tree_separator_delete_le T u v u (Or.inl rfl))
    have h2 := (hz2.symm.trans hwu).mono (tree_separator_delete_le T u v v (Or.inr rfl))
    have hb := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.1 hT.2 huv
    rw [SimpleGraph.isBridge_iff] at hb
    exact hb (h1.trans h2).symm
  have hsmall : f (Finset.univ.filter fun z => (T.deleteIncidenceSet u).Reachable v z) <
      f Finset.univ / 2 := by
    have h1 := hsup _ _ hdisj
    have h2 := hmono _ Finset.univ (Finset.subset_univ
      ((Finset.univ.filter fun z => (T.deleteIncidenceSet u).Reachable v z) ∪
        (Finset.univ.filter fun z => (T.deleteIncidenceSet v).Reachable w z)))
    linarith
  obtain ⟨x, hxu, hxheavy⟩ := heavy u
  have hxv : ¬ (T.deleteIncidenceSet u).Reachable x v := by
    intro h
    rw [comp_eq u x v h] at hxheavy
    linarith
  have hsub : (Finset.univ.filter fun z => (T.deleteIncidenceSet u).Reachable x z) ⊆
      (Finset.univ.filter fun z => (T.deleteIncidenceSet v).Reachable w z).erase u := by
    intro z hz
    rw [mem_comp] at hz
    rw [Finset.mem_erase, mem_comp]
    refine ⟨fun hzu => not_reach u x hxu (hzu ▸ hz), ?_⟩
    obtain ⟨q'⟩ := hT.1.preconnected x u
    obtain ⟨d', -, hd'1, hd'2⟩ := q'.exists_boundary_dart
      (↑(Finset.univ.filter fun z => (T.deleteIncidenceSet u).Reachable x z) : Set V)
      (by rw [Finset.mem_coe, mem_comp]) (by rw [Finset.mem_coe, mem_comp]; exact not_reach u x hxu)
    rw [Finset.mem_coe, mem_comp] at hd'1 hd'2
    have hfst' : d'.fst ≠ u := fun h => not_reach u x hxu (h ▸ hd'1)
    have hsnd' : d'.snd = u := by
      by_contra hne
      exact hd'2 (hd'1.trans (SimpleGraph.Adj.reachable
        (SimpleGraph.deleteIncidenceSet_adj.2 ⟨d'.adj, hfst', hne⟩)))
    have hyv : d'.fst ≠ v := fun h => hxv (h ▸ hd'1)
    have hall : ∀ t, (T.deleteIncidenceSet u).Reachable d'.fst t → t ≠ v :=
      fun t ht htv => hxv (htv ▸ hd'1.trans ht)
    have hyz : (T.deleteIncidenceSet u).Reachable d'.fst z := hd'1.symm.trans hz
    obtain ⟨pyz⟩ := hyz
    have h1 : (T.deleteIncidenceSet v).Reachable u d'.fst :=
      SimpleGraph.Adj.reachable (SimpleGraph.deleteIncidenceSet_adj.2
        ⟨hsnd' ▸ d'.adj.symm, hvu.symm, hyv⟩)
    exact hwu.trans (h1.trans (tree_separator_reachable_transfer T u v _ _ pyz hall))
  have hcard := lt_of_le_of_lt (Finset.card_le_card hsub)
    (Finset.card_erase_lt_of_mem ((mem_comp _ _ _).2 hwu))
  have := hmin (u, x) (by simp [P, hxu, hxheavy])
  simp only at this
  omega
