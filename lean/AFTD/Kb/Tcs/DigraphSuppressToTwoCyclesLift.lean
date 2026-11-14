import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSuppressTo
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphFinitePredecessorClosedSetCycle

/-!
# digraph_suppress_to_two_cycles_lift

Topic: graphs   Node: 9e49a601524a

Provenance: helper lemma. Cycle lifting under directed vertex suppression for the oriented twenty-cut profile.

If x has an arc to q, every pair of vertex-disjoint cycles after suppressing x into q lifts to a disjoint pair in the original digraph.
-/

set_option maxHeartbeats 2000000 in
/-- Every vertex of a directed cycle has an in-neighbour inside the cycle. -/
private lemma digraph_suppress_to_two_cycles_lift_cycle_predecessor {α : Type} [DecidableEq α]
    {D : Digraph α} {s : Finset α} (h : digraph_directed_cycle_on D s) :
    ∀ a ∈ s, ∃ b ∈ s, D.Adj b a := by
  classical
  obtain ⟨l, hnd, hlen, hts, hch, h0, t0, hhead, hlast, hcl⟩ := h
  have hne : l ≠ [] := by intro hl; rw [hl] at hlen; simp at hlen
  have ht0 : t0 ∈ l := by
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast; simp
  have h0mem : h0 ∈ l := by
    obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.mp hhead; simp
  intro a ha
  have ha' : a ∈ l := by rw [← List.mem_toFinset, hts]; exact ha
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp ha'
  have hkE : l[k.val]? = some a := by
    rw [List.getElem?_eq_getElem k.isLt]; exact congrArg some hk
  by_cases hk0 : k.val = 0
  · have hkE0 : l[0]? = some a := by rw [← hk0]; exact hkE
    have hhead_a : l.head? = some a := by
      rw [List.head?_eq_getElem?]; exact hkE0
    have h0eq : h0 = a := by
      have hh : some h0 = some a := by rw [← hhead, hhead_a]
      exact Option.some.inj hh
    refine ⟨t0, ?_, ?_⟩
    · rw [← hts, List.mem_toFinset]; exact ht0
    · rw [← h0eq]; exact hcl
  · have hJ : 1 ≤ k.val := by omega
    have hsplit := List.take_append_drop k.val l
    have hj := (List.isChain_append.mp (hsplit ▸ hch)).2.2
    have hdrop : (List.drop k.val l).head? = some a := by
      rw [List.head?_drop]; exact hkE
    have htake : (List.take k.val l).getLast? = some (l[(k.val - 1)]'(by omega)) := by
      rw [List.getLast?_take, if_neg (by omega : ¬ k.val = 0)]
      rw [List.getElem?_eq_getElem (by omega : k.val - 1 < l.length)]
      simp
    have hma : a ∈ (List.drop k.val l).head? := by rw [Option.mem_def]; exact hdrop
    have hml : l[(k.val - 1)]'(by omega) ∈ (List.take k.val l).getLast? := by
      rw [Option.mem_def]; exact htake
    refine ⟨l[(k.val-1)]'(by omega), ?_, hj _ hml _ hma⟩
    rw [← hts, List.mem_toFinset]
    exact List.getElem_mem (by omega)

set_option maxHeartbeats 2000000 in
/-- A directed cycle transports along an injective vertex map compatible with the arc relations. -/
private lemma digraph_suppress_to_two_cycles_lift_cycle_map {α β : Type} [DecidableEq α]
    [DecidableEq β] (f : β → α) (hf : Function.Injective f) (E : Digraph α) (R : β → β → Prop)
    (s : Finset β) (hR : ∀ a b, R a b → E.Adj (f a) (f b))
    (h : digraph_directed_cycle_on (⟨R⟩ : Digraph β) s) :
    digraph_directed_cycle_on E (s.image f) := by
  classical
  obtain ⟨l, hnd, hlen, hts, hch, a0, b0, hhead, hlast, hcl⟩ := h
  refine ⟨l.map f, List.Nodup.map hf hnd, ?_, ?_, ?_, f a0, f b0, ?_, ?_, ?_⟩
  · rw [List.length_map]; exact hlen
  · rw [← hts]
    ext a
    simp [List.mem_toFinset]
  · rw [List.isChain_map]
    exact List.IsChain.imp (fun a b hab => hR a b hab) hch
  · rw [List.head?_map, hhead]; rfl
  · rw [List.getLast?_map, hlast]; rfl
  · exact hR b0 a0 hcl

set_option maxHeartbeats 2000000 in
/-- A single cycle of the suppressed digraph lifts to a cycle of `D` inside its vertex image
enlarged by at most the vertex `x`. -/
private lemma digraph_suppress_to_two_cycles_lift_single {α : Type} [DecidableEq α]
    (D : Digraph α) (x q : α) (hxq : x ≠ q) (hx : D.Adj x q)
    (c : Finset {v : α // v ≠ x})
    (hcyc : digraph_directed_cycle_on (digraph_suppress_to D x q) c) :
    ∃ d : Finset α, digraph_directed_cycle_on D d ∧
      d ⊆ c.image Subtype.val ∪ {x} ∧
      (x ∈ d → (⟨q, fun h => hxq h.symm⟩ : {v : α // v ≠ x}) ∈ c) := by
  classical
  have hqx : q ≠ x := fun h => hxq h.symm
  set p : Finset α := c.image Subtype.val with hp
  set cond : Prop := (⟨q, hqx⟩ : {v : α // v ≠ x}) ∈ c ∧ ∃ u ∈ c, D.Adj u.val x with hcond
  set t : Finset α := p ∪ (if cond then {x} else ∅) with ht
  have ht_sub : t ⊆ p ∪ {x} := by
    intro z hz
    by_cases hc : cond
    · rw [ht, if_pos hc] at hz; exact hz
    · rw [ht, if_neg hc] at hz
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mp hz |>.resolve_right (by simp)))
  have hx_t : x ∈ t → cond := by
    intro hxint
    by_contra hc
    rw [ht, if_neg hc] at hxint
    obtain ⟨a, -, hav⟩ := Finset.mem_image.mp (Finset.mem_union.mp hxint |>.resolve_right (by simp))
    exact a.2 hav
  have hpred : ∀ v ∈ t, ∃ w ∈ t, D.Adj w v ∧ w ≠ v := by
    intro v hv
    by_cases hvp : v ∈ p
    · obtain ⟨a, hac, hav⟩ := Finset.mem_image.mp hvp
      obtain ⟨b, hbc, hbadj⟩ := digraph_suppress_to_two_cycles_lift_cycle_predecessor hcyc a hac
      obtain ⟨hbne, hgen | ⟨haq, hbx⟩⟩ := hbadj
      · refine ⟨b.val, ?_, ?_, ?_⟩
        · rw [ht]; exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨b, hbc, rfl⟩))
        · rw [← hav]; exact hgen
        · rw [← hav]; intro h; exact hbne (Subtype.ext h)
      · refine ⟨x, ?_, ?_, ?_⟩
        · have haeq : a = ⟨q, hqx⟩ := Subtype.ext haq
          have hqsc : (⟨q, hqx⟩ : {v : α // v ≠ x}) ∈ c := by rw [← haeq]; exact hac
          have hcond' : cond := ⟨hqsc, ⟨b, hbc, hbx⟩⟩
          rw [ht, if_pos hcond']; simp
        · rw [← hav, haq]; exact hx
        · rw [← hav, haq]; exact hxq
    · by_cases hc : cond
      · have hv' : v ∈ p ∪ ({x} : Finset α) := by rw [ht, if_pos hc] at hv; exact hv
        have hveq : v = x := by
          rcases Finset.mem_union.mp hv' with h | h
          · exact absurd h hvp
          · simpa using h
        obtain ⟨u, huc, hux⟩ := hc.2
        refine ⟨u.val, ?_, ?_, ?_⟩
        · rw [ht]; exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨u, huc, rfl⟩))
        · rw [hveq]; exact hux
        · rw [hveq]; exact u.2
      · rw [ht, if_neg hc] at hv
        exact absurd (Finset.mem_union.mp hv |>.resolve_right (by simp)) hvp
  have hcne : c.Nonempty := by
    obtain ⟨l, -, hlen, hts, -, -⟩ := hcyc
    refine ⟨l[0], ?_⟩
    rw [← hts, List.mem_toFinset]
    exact List.getElem_mem (by omega)
  have htne : t.Nonempty := by
    obtain ⟨a, ha⟩ := hcne
    exact ⟨a.val, by rw [ht]; exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨a, ha, rfl⟩))⟩
  let DT : Digraph {v : α // v ∈ t} := ⟨fun a b => D.Adj a.val b.val ∧ a.val ≠ b.val⟩
  have hDTloop : ∀ a, ¬ DT.Adj a a := fun a h => h.2 rfl
  have hDTpred : ∀ a ∈ (Finset.univ : Finset {v : α // v ∈ t}), ∃ b ∈ Finset.univ, DT.Adj b a := by
    intro a _
    obtain ⟨w, hwt, hwadj, hwne⟩ := hpred a.val a.2
    exact ⟨⟨w, hwt⟩, Finset.mem_univ _, hwadj, hwne⟩
  have hunivne : (Finset.univ : Finset {v : α // v ∈ t}).Nonempty := by
    obtain ⟨a, ha⟩ := htne
    exact ⟨⟨a, ha⟩, Finset.mem_univ _⟩
  obtain ⟨C, hCcyc, -⟩ := digraph_finite_predecessor_closed_set_cycle {v : α // v ∈ t} DT
    Finset.univ hunivne hDTloop hDTpred
  refine ⟨C.image Subtype.val, ?_, ?_, ?_⟩
  · exact digraph_suppress_to_two_cycles_lift_cycle_map Subtype.val Subtype.val_injective D DT.Adj
      C (fun a b h => h.1) hCcyc
  · intro z hz
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
    have h1 : a.val ∈ p ∪ {x} := ht_sub a.2
    rw [hp] at h1
    exact h1
  · intro hxint
    obtain ⟨a, -, hav⟩ := Finset.mem_image.mp hxint
    have hxt : x ∈ t := by rw [← hav]; exact a.2
    exact (hx_t hxt).1

theorem digraph_suppress_to_two_cycles_lift
    (α : Type) [DecidableEq α] (D : Digraph α) (x q : α) (hxq : x ≠ q)
    (hx : D.Adj x q)
    (c : Fin 2 → Finset {v : α // v ≠ x})
    (hcyc : ∀ i, digraph_directed_cycle_on (digraph_suppress_to D x q) (c i))
    (hdis : Pairwise (fun i j => Disjoint (c i) (c j))) :
    ∃ d : Fin 2 → Finset α, (∀ i, digraph_directed_cycle_on D (d i)) ∧
      Pairwise (fun i j => Disjoint (d i) (d j)) := by
  classical
  have hqx : q ≠ x := fun h => hxq h.symm
  have key : ∀ i : Fin 2, ∃ d : Finset α, digraph_directed_cycle_on D d ∧
      d ⊆ (c i).image Subtype.val ∪ {x} ∧
      (x ∈ d → (⟨q, hqx⟩ : {v : α // v ≠ x}) ∈ c i) :=
    fun i => digraph_suppress_to_two_cycles_lift_single D x q hxq hx (c i) (hcyc i)
  choose d hdcyc hdsub hdx using key
  refine ⟨d, hdcyc, ?_⟩
  intro i j hij
  have hdisij : ∀ ⦃a : {v : α // v ≠ x}⦄, a ∈ c i → a ∉ c j :=
    Finset.disjoint_left.mp (hdis hij)
  refine Finset.disjoint_left.mpr ?_
  intro z hzi hzj
  have hzi' := hdsub i hzi
  have hzj' := hdsub j hzj
  rcases Finset.mem_union.mp hzi' with hi | hi
  · rcases Finset.mem_union.mp hzj' with hj | hj
    · obtain ⟨a, hai, hav⟩ := Finset.mem_image.mp hi
      obtain ⟨b, hbj, hbv⟩ := Finset.mem_image.mp hj
      have hab : a = b := Subtype.ext (hav.trans hbv.symm)
      subst hab
      exact hdisij hai hbj
    · rw [Finset.mem_singleton] at hj
      obtain ⟨a, hai, hav⟩ := Finset.mem_image.mp hi
      exact a.2 (hav.trans hj)
  · rw [Finset.mem_singleton] at hi
    rcases Finset.mem_union.mp hzj' with hj | hj
    · obtain ⟨b, hbj, hbv⟩ := Finset.mem_image.mp hj
      exact b.2 (hbv.trans hi)
    · rw [Finset.mem_singleton] at hj
      exact hdisij (hdx i (by rw [← hi]; exact hzi)) (hdx j (by rw [← hj]; exact hzj))
