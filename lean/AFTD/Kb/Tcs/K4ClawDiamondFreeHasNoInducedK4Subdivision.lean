import AFTD.Prelude
import AFTD.Kb.Tcs.HasInducedK4Subdivision
import AFTD.Kb.Tcs.IsClawFree
import AFTD.Kb.Tcs.IsDiamondFree
import AFTD.Kb.Tcs.Support
import AFTD.Kb.Tcs.DiamondGraph

/-!
# k4_claw_diamond_free_has_no_induced_k4_subdivision

Topic: graphs   Node: 0b3700003226

Provenance: helper lemma. Helper for arXiv:2610.32404 Proposition 11.2 (PR-412), following the local path argument of Lemma 11.1. Stated for arbitrary simple graphs: only the finite union of the six paths is used.

Every simple graph containing neither an induced K4, an induced claw, nor an induced diamond contains no induced subdivision of K4.
-/

namespace K4ClawDiamondFree

private def M6 (x01 x02 x03 x12 x13 x23 : Bool) (i j : Fin 4) : Bool :=
  match i.val, j.val with
  | 0, 1 => x01 | 1, 0 => x01
  | 0, 2 => x02 | 2, 0 => x02
  | 0, 3 => x03 | 3, 0 => x03
  | 1, 2 => x12 | 2, 1 => x12
  | 1, 3 => x13 | 3, 1 => x13
  | 2, 3 => x23 | 3, 2 => x23
  | _, _ => false

private lemma finite_case : ∀ x01 x02 x03 x12 x13 x23 : Bool,
    (∀ r : Fin 4, ∃ o1 o2 : Fin 4, o1 ≠ o2 ∧ r ≠ o1 ∧ r ≠ o2 ∧
      M6 x01 x02 x03 x12 x13 x23 r o1 = true ∧ M6 x01 x02 x03 x12 x13 x23 r o2 = true ∧
      M6 x01 x02 x03 x12 x13 x23 o1 o2 = true) →
    (∀ i j : Fin 4, i ≠ j → M6 x01 x02 x03 x12 x13 x23 i j = true) ∨
    ∃ i j k l : Fin 4, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      M6 x01 x02 x03 x12 x13 x23 i j = false ∧ M6 x01 x02 x03 x12 x13 x23 i k = true ∧
      M6 x01 x02 x03 x12 x13 x23 i l = true ∧ M6 x01 x02 x03 x12 x13 x23 j k = true ∧
      M6 x01 x02 x03 x12 x13 x23 j l = true ∧ M6 x01 x02 x03 x12 x13 x23 k l = true := by
  decide

private def E (i j : Fin 4) : {ij : Fin 4 × Fin 4 // ij.1 < ij.2} :=
  if h : i < j then ⟨(i, j), h⟩ else if h' : j < i then ⟨(j, i), h'⟩ else ⟨(0, 1), by decide⟩

private lemma E_ends : ∀ i j : Fin 4, i ≠ j →
    ((E i j).val.1 = i ∧ (E i j).val.2 = j) ∨ ((E i j).val.1 = j ∧ (E i j).val.2 = i) := by
  decide

private lemma E_ne : ∀ r o1 o2 : Fin 4, o1 ≠ o2 → r ≠ o1 → r ≠ o2 → E r o1 ≠ E r o2 := by
  decide

private lemma o_ne : ∀ (r : Fin 4) (t : Fin 3), r ≠ r + t.succ := by decide

private lemma o_inj : ∀ (r : Fin 4) (t1 t2 : Fin 3), t1 ≠ t2 → r + t1.succ ≠ r + t2.succ := by decide


set_option maxHeartbeats 1000000 in
private theorem main {α : Type*} (G : SimpleGraph α)
    (hK : ¬ SimpleGraph.IsIndContained (⊤ : SimpleGraph (Fin 4)) G)
    (hc : IsClawFree G) (hd : is_diamond_free G) :
    ¬ has_induced_k4_subdivision G := by
  classical
  rintro ⟨b, hb, P, _hpath, hbr, hsh, hind⟩
  have hbrE : ∀ i j l : Fin 4, i ≠ j → b l ∈ (P (E i j)).support → l = i ∨ l = j := by
    intro i j l hij hl
    rcases hbr (E i j) l hl with h | h <;> rcases E_ends i j hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (h.trans h1)
    · exact Or.inr (h.trans h1)
    · exact Or.inr (h.trans h2)
    · exact Or.inl (h.trans h2)
  have hnb : ∀ r o : Fin 4, r ≠ o → ∃ n, G.Adj (b r) n ∧ n ∈ (P (E r o)).support := by
    intro r o hro
    have hlen : 0 < (P (E r o)).length := by
      rcases Nat.eq_zero_or_pos (P (E r o)).length with h | h
      · exfalso
        have h0 := hb (SimpleGraph.Walk.eq_of_length_eq_zero h)
        exact absurd h0 (ne_of_lt (E r o).2)
      · exact h
    rcases E_ends r o hro with ⟨h1, _⟩ | ⟨_, h2⟩
    · refine ⟨(P (E r o)).getVert 1, ?_, (P (E r o)).getVert_mem_support 1⟩
      have h := (P (E r o)).adj_getVert_succ (i := 0) hlen
      rw [SimpleGraph.Walk.getVert_zero] at h
      have hb1 : b (E r o).val.1 = b r := by rw [h1]
      rw [← hb1]
      exact h
    · refine ⟨(P (E r o)).getVert ((P (E r o)).length - 1), ?_,
        (P (E r o)).getVert_mem_support _⟩
      have h := (P (E r o)).adj_getVert_succ (i := (P (E r o)).length - 1) (by omega)
      rw [Nat.sub_add_cancel hlen, SimpleGraph.Walk.getVert_length] at h
      have hb2 : b (E r o).val.2 = b r := by rw [h2]
      rw [← hb2]
      exact h.symm
  have hid : ∀ (r o : Fin 4) (v : α) (f : {ij : Fin 4 × Fin 4 // ij.1 < ij.2}), r ≠ o →
      v ∈ (P (E r o)).support → v ∈ (P f).support → f ≠ E r o → G.Adj (b r) v → v = b o := by
    intro r o v f hro hv1 hv2 hf hadj
    obtain ⟨l, rfl⟩ := hsh (E r o) f (Ne.symm hf) v hv1 hv2
    rcases hbrE r o l hro hv1 with h | h
    · subst h
      exact absurd hadj (G.loopless.irrefl _)
    · rw [h]
  have key : ∀ (r o1 o2 : Fin 4) (n1 n2 : α), o1 ≠ o2 → r ≠ o1 → r ≠ o2 →
      G.Adj (b r) n1 → n1 ∈ (P (E r o1)).support →
      G.Adj (b r) n2 → n2 ∈ (P (E r o2)).support →
      n1 ≠ n2 ∧ (G.Adj n1 n2 → n1 = b o1 ∧ n2 = b o2) := by
    intro r o1 o2 n1 n2 h12 hr1 hr2 ha1 hm1 ha2 hm2
    have hE := E_ne r o1 o2 h12 hr1 hr2
    refine ⟨?_, ?_⟩
    · intro heq
      subst heq
      have e1 := hid r o1 n1 (E r o2) hr1 hm1 hm2 (Ne.symm hE) ha1
      have e2 := hid r o2 n1 (E r o1) hr2 hm2 hm1 hE ha2
      exact h12 (hb (e1.symm.trans e2))
    · intro hadj
      obtain ⟨f, hf⟩ := hind n1 n2 ⟨_, hm1⟩ ⟨_, hm2⟩ hadj
      have hf1 := (P f).fst_mem_support_of_mem_edges hf
      have hf2 := (P f).snd_mem_support_of_mem_edges hf
      by_cases hfa : f = E r o1
      · exfalso
        subst hfa
        have e2 := hid r o2 n2 (E r o1) hr2 hm2 hf2 hE ha2
        rw [e2] at hf2
        rcases hbrE r o1 o2 hr1 hf2 with h | h
        · exact hr2 h.symm
        · exact h12 h.symm
      · have e1 := hid r o1 n1 f hr1 hm1 hf1 hfa ha1
        by_cases hfb : f = E r o2
        · exfalso
          subst hfb
          rw [e1] at hf1
          rcases hbrE r o2 o1 hr2 hf1 with h | h
          · exact hr1 h.symm
          · exact h12 h
        · exact ⟨e1, hid r o2 n2 f hr2 hm2 hf2 hfb ha2⟩
  have htri : ∀ r : Fin 4, ∃ o1 o2 : Fin 4, o1 ≠ o2 ∧ r ≠ o1 ∧ r ≠ o2 ∧
      G.Adj (b r) (b o1) ∧ G.Adj (b r) (b o2) ∧ G.Adj (b o1) (b o2) := by
    intro r
    by_contra hno
    push Not at hno
    choose n hn using fun t : Fin 3 => hnb r (r + t.succ) (o_ne r t)
    have hleaf : ∀ t1 t2 : Fin 3, t1 ≠ t2 → n t1 ≠ n t2 ∧ ¬ G.Adj (n t1) (n t2) := by
      intro t1 t2 ht
      obtain ⟨hne, hadj⟩ := key r _ _ (n t1) (n t2) (o_inj r t1 t2 ht) (o_ne r t1) (o_ne r t2)
        (hn t1).1 (hn t1).2 (hn t2).1 (hn t2).2
      refine ⟨hne, fun h => ?_⟩
      obtain ⟨e1, e2⟩ := hadj h
      have a1 := (hn t1).1
      have a2 := (hn t2).1
      rw [e1] at a1 h
      rw [e2] at a2 h
      exact hno _ _ (o_inj r t1 t2 ht) (o_ne r t1) (o_ne r t2) a1 a2 h
    apply hc
    let f : Fin 1 ⊕ Fin 3 → α := fun x => match x with
      | .inl _ => b r
      | .inr t => n t
    refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
    · intro x y hxy
      rcases x with x | x <;> rcases y with y | y
      · rw [Subsingleton.elim x y]
      · exact absurd hxy (G.ne_of_adj (hn y).1)
      · exact absurd hxy.symm (G.ne_of_adj (hn x).1)
      · by_cases hxy' : x = y
        · rw [hxy']
        · exact absurd hxy (hleaf x y hxy').1
    · intro x y
      change G.Adj (f x) (f y) ↔ (completeBipartiteGraph (Fin 1) (Fin 3)).Adj x y
      rcases x with x | x <;> rcases y with y | y
      · simp [f, completeBipartiteGraph]
      · simp [f, completeBipartiteGraph, (hn y).1]
      · simp [f, completeBipartiteGraph, ((hn x).1).symm]
      · have hnot : ¬ G.Adj (n x) (n y) := by
          by_cases hxy' : x = y
          · rw [hxy']
            exact G.loopless.irrefl _
          · exact (hleaf x y hxy').2
        simp [f, completeBipartiteGraph, hnot]
  let M : Fin 4 → Fin 4 → Bool := fun i j => decide (G.Adj (b i) (b j))
  have hM : ∀ i j, M i j = M6 (M 0 1) (M 0 2) (M 0 3) (M 1 2) (M 1 3) (M 2 3) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [M6, M] <;> exact G.adj_comm _ _
  have hA : ∀ i j, G.Adj (b i) (b j) ↔
      M6 (M 0 1) (M 0 2) (M 0 3) (M 1 2) (M 1 3) (M 2 3) i j = true := by
    intro i j
    rw [← hM]
    simp [M]
  have htriM : ∀ r : Fin 4, ∃ o1 o2 : Fin 4, o1 ≠ o2 ∧ r ≠ o1 ∧ r ≠ o2 ∧
      M6 (M 0 1) (M 0 2) (M 0 3) (M 1 2) (M 1 3) (M 2 3) r o1 = true ∧
      M6 (M 0 1) (M 0 2) (M 0 3) (M 1 2) (M 1 3) (M 2 3) r o2 = true ∧
      M6 (M 0 1) (M 0 2) (M 0 3) (M 1 2) (M 1 3) (M 2 3) o1 o2 = true := by
    intro r
    obtain ⟨o1, o2, h1, h2, h3, h4, h5, h6⟩ := htri r
    exact ⟨o1, o2, h1, h2, h3, (hA _ _).1 h4, (hA _ _).1 h5, (hA _ _).1 h6⟩
  rcases finite_case _ _ _ _ _ _ htriM with hall | ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl,
      mij, mik, mil, mjk, mjl, mkl⟩
  · apply hK
    refine ⟨⟨⟨b, hb⟩, ?_⟩⟩
    intro x y
    simp only [Function.Embedding.coeFn_mk, SimpleGraph.top_adj]
    constructor
    · intro h hxy
      subst hxy
      exact G.loopless.irrefl _ h
    · intro hxy
      exact (hA x y).2 (hall x y hxy)
  · apply hd
    have hA' : ∀ x y, ¬ G.Adj (b x) (b y) ↔
        M6 (M 0 1) (M 0 2) (M 0 3) (M 1 2) (M 1 3) (M 2 3) x y = false := by
      intro x y
      rw [hA]
      simp
    have aij := (hA' i j).2 mij
    have aji : ¬ G.Adj (b j) (b i) := fun h => aij h.symm
    have aik := (hA i k).2 mik
    have ail := (hA i l).2 mil
    have ajk := (hA j k).2 mjk
    have ajl := (hA j l).2 mjl
    have akl := (hA k l).2 mkl
    clear hM hA hA' htri htriM key hid hnb hbrE hind hsh hbr
    have hg : Function.Injective (![i, k, l, j] : Fin 4 → Fin 4) := by
      intro x y h
      fin_cases x <;> fin_cases y <;> simp at h ⊢ <;> simp_all [eq_comm]
    refine ⟨⟨⟨fun x => b ((![i, k, l, j] : Fin 4 → Fin 4) x), hb.comp hg⟩, ?_⟩⟩
    intro x y
    change G.Adj (b ((![i, k, l, j] : Fin 4 → Fin 4) x)) (b ((![i, k, l, j] : Fin 4 → Fin 4) y)) ↔
      diamond_graph.Adj x y
    fin_cases x <;> fin_cases y <;>
      simp [diamond_graph, SimpleGraph.deleteEdges_adj, aik, ail, ajk, ajl, akl, aij, aji,
        aik.symm, ail.symm, ajk.symm, ajl.symm, akl.symm, G.loopless.irrefl]

end K4ClawDiamondFree

theorem k4_claw_diamond_free_has_no_induced_k4_subdivision {V : Type*} (G : SimpleGraph V)
    (hK : ¬ SimpleGraph.IsIndContained (⊤ : SimpleGraph (Fin 4)) G)
    (hc : IsClawFree G) (hd : is_diamond_free G) :
    ¬ has_induced_k4_subdivision G := K4ClawDiamondFree.main G hK hc hd
