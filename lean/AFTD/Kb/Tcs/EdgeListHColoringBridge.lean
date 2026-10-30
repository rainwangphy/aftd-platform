import AFTD.Prelude
import AFTD.Kb.Tcs.EdgeListConnectedCubic
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# edge_list_h_coloring_bridge

Topic: np_completeness   Node: 156e8ec14e7d

Provenance: formalization of a published result. Source: arXiv:2610.35794 (Computational complexity of the H-coloring problem in cubic graphs), Lemma 1(B) (quoted from its ref. [8]): an H-coloring maps bridges of G to bridges of H; here H simple and cubic, G a loopless cubic multigraph given as an edge list

For a type W : Type* (any universe), let H be a simple graph on W in which every vertex x lies in exactly 3 edges ((H.incidenceSet x).ncard = 3), let es be an edge list with edge_list_connected_cubic n es, and let f : Fin es.length → H.edgeSet be an H-coloring of it (for every v < n some x : W has the image of {i | es[i].1 = v ∨ es[i].2 = v} under f equal to H.incidenceSet x). If edge i is a bridge of the multigraph, i.e. the simple graph SimpleGraph.fromRel on Fin n relating u and v when some edge j ≠ i has es[j].1 = u.val ∧ es[j].2 = v.val is not Connected, then f i is a bridge of H: H.IsBridge (f i).
-/

theorem edge_list_h_coloring_bridge {W : Type*} (H : SimpleGraph W)
    (hH : ∀ x : W, (H.incidenceSet x).ncard = 3) (n : ℕ) (es : List (ℕ × ℕ))
    (hG : edge_list_connected_cubic n es) (f : Fin es.length → H.edgeSet)
    (hf : ∀ v : ℕ, v < n → ∃ x : W,
      (fun i => (f i : Sym2 W)) '' {i | es[i].1 = v ∨ es[i].2 = v} = H.incidenceSet x)
    (i : Fin es.length)
    (hi : ¬ (SimpleGraph.fromRel (fun u v : Fin n =>
      ∃ j : Fin es.length, j ≠ i ∧ es[j].1 = u.val ∧ es[j].2 = v.val)).Connected) :
    H.IsBridge (f i) := by
  classical
  obtain ⟨hE, hdeg, hconn⟩ := hG
  set G' : SimpleGraph (Fin n) := SimpleGraph.fromRel (fun u v : Fin n =>
      ∃ j : Fin es.length, j ≠ i ∧ es[j].1 = u.val ∧ es[j].2 = v.val) with hG'
  set u0 : Fin n := ⟨es[i].1, (hE i).1⟩ with hu0def
  set v0 : Fin n := ⟨es[i].2, (hE i).2.1⟩ with hv0def
  have hnr : ¬ G'.Reachable u0 v0 := by
    intro hr
    apply hi
    have key : ∀ u v : Fin n, (SimpleGraph.fromRel (fun u v : Fin n =>
        ∃ i : Fin es.length, es[i].1 = u.val ∧ es[i].2 = v.val)).Adj u v → G'.Reachable u v := by
      intro u v huv
      rw [SimpleGraph.fromRel_adj] at huv
      obtain ⟨hne, ⟨j, h1, h2⟩ | ⟨j, h1, h2⟩⟩ := huv
      · by_cases hj : j = i
        · have hu : u = u0 := Fin.ext (by rw [← h1, hj])
          have hv : v = v0 := Fin.ext (by rw [← h2, hj])
          rw [hu, hv]; exact hr
        · exact SimpleGraph.Adj.reachable (by
            rw [hG', SimpleGraph.fromRel_adj]; exact ⟨hne, Or.inl ⟨j, hj, h1, h2⟩⟩)
      · by_cases hj : j = i
        · have hv : v = u0 := Fin.ext (by rw [← h1, hj])
          have hu : u = v0 := Fin.ext (by rw [← h2, hj])
          rw [hu, hv]; exact hr.symm
        · exact SimpleGraph.Adj.reachable (by
            rw [hG', SimpleGraph.fromRel_adj]; exact ⟨hne, Or.inr ⟨j, hj, h1, h2⟩⟩)
    haveI : Nonempty (Fin n) := hconn.nonempty
    refine ⟨fun u v => ?_⟩
    obtain ⟨p⟩ := hconn.preconnected u v
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons h _ ih => exact (key _ _ h).trans ih
  set S : Finset (Fin n) := Finset.univ.filter (fun w => G'.Reachable u0 w) with hS
  have hu0 : u0 ∈ S := by simp [hS]
  have hv0 : v0 ∉ S := by simpa [hS] using hnr
  have hclos : ∀ j : Fin es.length, j ≠ i → ∀ (a b : Fin n), es[j].1 = a.val → es[j].2 = b.val →
      (a ∈ S ↔ b ∈ S) := by
    intro j hj a b ha hb
    have hadj : G'.Adj a b := by
      rw [hG', SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl ⟨j, hj, ha, hb⟩⟩
      intro hab; apply (hE j).2.2; rw [ha, hb, hab]
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
  have hf' : ∀ v : Fin n, ∃ x : W, (fun j => (f j : Sym2 W)) ''
      {j | es[j].1 = v.val ∨ es[j].2 = v.val} = H.incidenceSet x := fun v => hf v.val v.isLt
  choose z hz using hf'
  have PV : ∀ (v : Fin n) (h : Sym2 W), (∑ j : Fin es.length,
      if (es[j].1 = v.val ∨ es[j].2 = v.val) ∧ (f j : Sym2 W) = h then (1 : ZMod 2) else 0) =
      if h ∈ H.incidenceSet (z v) then 1 else 0 := by
    intro v h
    set T := Finset.univ.filter (fun j : Fin es.length => es[j].1 = v.val ∨ es[j].2 = v.val) with hT
    have hTc : T.card = 3 := hdeg v.val v.isLt
    have himg : ((T.image (fun j => (f j : Sym2 W)) : Finset (Sym2 W)) : Set (Sym2 W)) =
        H.incidenceSet (z v) := by
      rw [← hz v]; ext e; simp [hT]
    have hinj : Set.InjOn (fun j => (f j : Sym2 W)) T := by
      rw [← Finset.card_image_iff, hTc, ← Set.ncard_coe_finset, himg, hH]
    rw [Finset.sum_boole]
    split_ifs with hmem
    · rw [← himg, Finset.mem_coe, Finset.mem_image] at hmem
      obtain ⟨j0, hj0T, hj0⟩ := hmem
      have : Finset.univ.filter (fun j : Fin es.length =>
          (es[j].1 = v.val ∨ es[j].2 = v.val) ∧ (f j : Sym2 W) = h) = {j0} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hjv, hjh⟩
          exact hinj (by simpa [hT] using hjv) hj0T (hjh.trans hj0.symm)
        · rintro rfl; exact ⟨by simpa [hT] using hj0T, hj0⟩
      rw [this]; simp
    · have : Finset.univ.filter (fun j : Fin es.length =>
          (es[j].1 = v.val ∨ es[j].2 = v.val) ∧ (f j : Sym2 W) = h) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro j - ⟨hjv, hjh⟩
        apply hmem
        rw [← himg, Finset.mem_coe, Finset.mem_image]
        exact ⟨j, by simpa [hT] using hjv, hjh⟩
      rw [this]; simp
  have PJ : ∀ (j : Fin es.length) (h : Sym2 W), (∑ v ∈ S,
      if (es[j].1 = v.val ∨ es[j].2 = v.val) ∧ (f j : Sym2 W) = h then (1 : ZMod 2) else 0) =
      if j = i ∧ (f j : Sym2 W) = h then 1 else 0 := by
    intro j h
    by_cases hgh : (f j : Sym2 W) = h
    swap
    · simp [hgh]
    simp only [hgh, and_true]
    have hsplit : ∀ v : Fin n, (if es[j].1 = v.val ∨ es[j].2 = v.val then (1 : ZMod 2) else 0) =
        (if (⟨es[j].1, (hE j).1⟩ : Fin n) = v then 1 else 0) +
          (if (⟨es[j].2, (hE j).2.1⟩ : Fin n) = v then 1 else 0) := by
      intro v
      have hne := (hE j).2.2
      simp only [Fin.ext_iff, Fin.getElem_fin] at hne ⊢
      by_cases h1 : es[(j : ℕ)].1 = v.val <;> by_cases h2 : es[(j : ℕ)].2 = v.val
      · exact absurd (h1.trans h2.symm) hne
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
    rw [Finset.sum_congr rfl (fun v _ => hsplit v), Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.sum_ite_eq]
    by_cases hji : j = i
    · have ha : (⟨es[j].1, (hE j).1⟩ : Fin n) = u0 := Fin.ext (congrArg (fun k : Fin es.length => es[k].1) hji)
      have hb : (⟨es[j].2, (hE j).2.1⟩ : Fin n) = v0 := Fin.ext (congrArg (fun k : Fin es.length => es[k].2) hji)
      rw [if_pos hji, ha, hb, if_pos hu0, if_neg hv0]; simp
    · rw [if_neg hji]
      have := hclos j hji ⟨es[j].1, (hE j).1⟩ ⟨es[j].2, (hE j).2.1⟩ rfl rfl
      by_cases ha : (⟨es[j].1, (hE j).1⟩ : Fin n) ∈ S
      · rw [if_pos ha, if_pos (this.mp ha)]; decide
      · rw [if_neg ha, if_neg (fun hb => ha (this.mpr hb))]; simp
  set N : W → ZMod 2 := fun x => ∑ v ∈ S, if z v = x then 1 else 0 with hN
  have main : ∀ x y, H.Adj x y → N x + N y = if (f i : Sym2 W) = s(x, y) then 1 else 0 := by
    intro x y hxy
    have hm : ∀ w, s(x, y) ∈ H.incidenceSet w ↔ (w = x ∨ w = y) := fun w => by
      simp [SimpleGraph.incidenceSet, hxy, Sym2.mem_iff]
    have h1 : ∑ v ∈ S, ∑ j : Fin es.length, (if (es[j].1 = v.val ∨ es[j].2 = v.val) ∧
        (f j : Sym2 W) = s(x, y) then (1 : ZMod 2) else 0) = N x + N y := by
      rw [Finset.sum_congr rfl (fun v _ => PV v s(x, y)), hN, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have hne := hxy.ne
      simp only [hm]
      by_cases h1 : z v = x <;> by_cases h2 : z v = y
      · exact absurd (h1.symm.trans h2) hne
      · simp [h1, h2, hne]
      · simp [h1, h2, hne.symm]
      · simp [h1, h2]
    rw [← h1, Finset.sum_comm, Finset.sum_congr rfl (fun j _ => PJ j s(x, y))]
    simp only [ite_and]
    rw [Finset.sum_ite_eq']
    simp
  obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (f i : Sym2 W)
  change s(a, b) = _ at hab
  have hadj : H.Adj a b := by
    have := (f i).2
    rw [← hab] at this
    exact this
  rw [← hab, SimpleGraph.isBridge_iff]
  intro hr
  have z2 : ∀ p q : ZMod 2, p + q = 0 → p = q := by decide
  have hconst : ∀ x y, (H.deleteEdges {s(a, b)}).Walk x y → N x = N y := by
    intro x y p
    induction p with
    | nil => rfl
    | cons h _ ih =>
      rw [← ih]
      simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at h
      have h2 := main _ _ h.1
      rw [if_neg] at h2
      · exact z2 _ _ h2
      · intro heq
        rw [← hab] at heq
        exact h.2 heq.symm
  obtain ⟨p⟩ := hr
  have e1 := hconst _ _ p
  have e2 := main a b hadj
  rw [← hab, if_pos rfl, ← e1] at e2
  have z3 : ∀ t : ZMod 2, t + t ≠ 1 := by decide
  exact z3 _ e2
