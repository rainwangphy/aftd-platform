import AFTD.Prelude

/-!
# simple_graph_is_tree_nonempty_iso_path_graph_of_degree_le_two

Topic: graphs   Node: 559a5af074ac

Provenance: helper lemma. Helper for arXiv:2610.12109 (Sharp linear Turán remainders for cycle and edge extremality), Lemma 2.5 (equality case of the lower bound: the extremal tree is a path).

A finite tree in which every vertex has degree at most 2 is isomorphic to the path P_k, k = |V|.
-/

theorem simple_graph_is_tree_nonempty_iso_path_graph_of_degree_le_two {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree)
    (hdeg : ∀ v, G.degree v ≤ 2) : Nonempty (G ≃g SimpleGraph.pathGraph (Fintype.card V)) := by
  classical
  let P : ℕ → Prop := fun n => ∃ u v : V, ∃ p : G.Walk u v, p.IsPath ∧ p.length = n
  obtain ⟨u₀⟩ := hT.1.nonempty
  have hP0 : P 0 := ⟨u₀, u₀, .nil, SimpleGraph.Walk.IsPath.nil, rfl⟩
  obtain ⟨u, v, p, hp, hpN⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le (Fintype.card V)) hP0
  have hmax : ∀ u' v' (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length := fun u' v' q hq => by
    rw [hpN]
    exact Nat.le_findGreatest hq.length_lt.le ⟨u', v', q, hq, rfl⟩
  -- the longest path visits every vertex
  have hall : ∀ x, x ∈ p.support := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx⟩ := hcon
    obtain ⟨q⟩ := hT.1.preconnected u x
    obtain ⟨d, -, hd1, hd2⟩ := q.exists_boundary_dart {y | y ∈ p.support} p.start_mem_support hx
    simp only [Set.mem_setOf_eq] at hd1 hd2
    obtain ⟨i, hi, hile⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hd1
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · have hau : d.fst = u := by rw [← hi, p.getVert_zero]
      have hadj : G.Adj d.snd u := hau ▸ d.adj.symm
      have := hmax _ _ (SimpleGraph.Walk.cons hadj p) (hp.cons hd2)
      simp at this
    · rcases eq_or_lt_of_le hile with heq | hlt
      · have hav : d.fst = v := by rw [← hi, heq, p.getVert_length]
        have hadj : G.Adj v d.snd := hav ▸ d.adj
        have := hmax _ _ (p.concat hadj) (hp.concat hd2 hadj)
        simp [SimpleGraph.Walk.length_concat] at this
      · have h1 : G.Adj d.fst (p.getVert (i - 1)) := by
          have := p.adj_getVert_succ (i := i - 1) (by omega)
          rw [Nat.sub_add_cancel hipos, hi] at this
          exact this.symm
        have h2 : G.Adj d.fst (p.getVert (i + 1)) := by
          have := p.adj_getVert_succ (i := i) hlt
          rwa [hi] at this
        have h3 : G.Adj d.fst d.snd := d.adj
        have hne12 : p.getVert (i - 1) ≠ p.getVert (i + 1) := fun h => by
          have := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
            (by simp only [Set.mem_setOf_eq]; omega) h
          omega
        have hne13 : p.getVert (i - 1) ≠ d.snd := fun h => hd2 (h ▸ p.getVert_mem_support _)
        have hne23 : p.getVert (i + 1) ≠ d.snd := fun h => hd2 (h ▸ p.getVert_mem_support _)
        have h3le : 3 ≤ G.degree d.fst := by
          rw [← G.card_neighborFinset_eq_degree]
          have hsub : ({p.getVert (i - 1), p.getVert (i + 1), d.snd} : Finset V) ⊆
              G.neighborFinset d.fst := by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rw [SimpleGraph.mem_neighborFinset]
            rcases hy with rfl | rfl | rfl <;> assumption
          calc 3 = ({p.getVert (i - 1), p.getVert (i + 1), d.snd} : Finset V).card := by
                rw [Finset.card_insert_of_notMem (by simp [hne12, hne13]), Finset.card_pair hne23]
            _ ≤ _ := Finset.card_le_card hsub
        have := hdeg d.fst
        omega
  have hlen : p.length + 1 = Fintype.card V := by
    have huniv : p.support.toFinset = Finset.univ :=
      Finset.eq_univ_of_forall fun x => List.mem_toFinset.2 (hall x)
    rw [← Finset.card_univ, ← huniv, List.toFinset_card_of_nodup hp.support_nodup,
      p.length_support]
  let φ : Fin (Fintype.card V) → V := fun i => p.getVert i
  have hinj : Function.Injective φ := fun i j h =>
    Fin.ext (hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) h)
  have hsurj : Function.Surjective φ := fun x => by
    obtain ⟨n, hn, hnl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 (hall x)
    exact ⟨⟨n, by omega⟩, hn⟩
  -- every edge is an edge of the path: the path already has |E| = card V − 1 edges
  have hedge : ∀ a b, G.Adj a b →
      ∃ m : ℕ, m < p.length ∧ s(a, b) = s(p.getVert m, p.getVert (m + 1)) := by
    intro a b hab
    let f : Fin p.length → Sym2 V := fun m => s(p.getVert m, p.getVert (m + 1))
    have hfinj : Function.Injective f := by
      intro m m' h
      simp only [f, Sym2.eq_iff] at h
      rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact Fin.ext (hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
          (by simp only [Set.mem_setOf_eq]; omega) h1)
      · have e1 := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
          (by simp only [Set.mem_setOf_eq]; omega) h1
        have e2 := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
          (by simp only [Set.mem_setOf_eq]; omega) h2
        omega
    have hsub : Finset.univ.image f ⊆ G.edgeFinset := by
      intro e he
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at he
      obtain ⟨m, rfl⟩ := he
      rw [SimpleGraph.mem_edgeFinset]
      exact p.adj_getVert_succ m.2
    have hcard : G.edgeFinset.card ≤ (Finset.univ.image f).card := by
      rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
      have := hT.card_edgeFinset
      omega
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hmem : s(a, b) ∈ G.edgeFinset := by rwa [SimpleGraph.mem_edgeFinset]
    rw [← heq] at hmem
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hmem
    obtain ⟨m, hm⟩ := hmem
    exact ⟨m, m.2, hm.symm⟩
  let e : Fin (Fintype.card V) ≃ V := Equiv.ofBijective φ ⟨hinj, hsurj⟩
  refine ⟨⟨e.symm, @fun a b => ?_⟩⟩
  obtain ⟨i, rfl⟩ := hsurj a
  obtain ⟨j, rfl⟩ := hsurj b
  have hi : e.symm (φ i) = i := e.symm_apply_apply i
  have hj : e.symm (φ j) = j := e.symm_apply_apply j
  rw [hi, hj, SimpleGraph.pathGraph_adj]
  constructor
  · rintro (h | h)
    · have := p.adj_getVert_succ (i := i) (by omega)
      simp only [φ]
      rwa [show (j : ℕ) = i + 1 by omega]
    · have := p.adj_getVert_succ (i := j) (by omega)
      simp only [φ]
      rw [show (i : ℕ) = j + 1 by omega]
      exact this.symm
  · intro hadj
    obtain ⟨m, hm, hmeq⟩ := hedge _ _ hadj
    rw [Sym2.eq_iff] at hmeq
    rcases hmeq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) h1
      have e2 := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) h2
      left
      omega
    · have e1 := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) h1
      have e2 := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) h2
      right
      omega
