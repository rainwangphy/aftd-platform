import AFTD.Prelude
import AFTD.Kb.Tcs.IsFeasiblePacking
import AFTD.Kb.Tcs.IncidentEdgeMultiset

/-!
# op_1627_not_realizable_parameters_four_three_two_two

Topic: combinatorics   Node: e9053aa349b6

Provenance: formalization of a published result. Source: arXiv:2611.15376 Sec. 4.2, Theorem 4.3

There does not exist an edge-coloring ϕ : (⊤ : SimpleGraph (Fin 5)).edgeSet → Finset (Fin 4) assigning a 3-element subset of Fin 4 to each edge of the complete graph on Fin 5 such that for every vertex v : Fin 5, the multiset of incident edge labels incident_edge_multiset ϕ v is a feasible packing for parameters (4, 3, 2, 2).
-/

open scoped Sym2
open Finset

noncomputable def op_1627_not_realizable_parameters_four_three_two_two_pl
    (φ : (⊤ : SimpleGraph (Fin 5)).edgeSet → Finset (Fin 4)) (e : Sym2 (Fin 5)) : Finset (Fin 4) :=
  if h : e ∈ (⊤ : SimpleGraph (Fin 5)).edgeSet then φ ⟨e, h⟩ else ∅

lemma op_1627_not_realizable_parameters_four_three_two_two_pl_pos
    (φ : (⊤ : SimpleGraph (Fin 5)).edgeSet → Finset (Fin 4)) (e : Sym2 (Fin 5))
    (h : e ∈ (⊤ : SimpleGraph (Fin 5)).edgeSet) :
    op_1627_not_realizable_parameters_four_three_two_two_pl φ e = φ ⟨e, h⟩ := by
  unfold op_1627_not_realizable_parameters_four_three_two_two_pl; rw [dif_pos h]

lemma op_1627_not_realizable_parameters_four_three_two_two_pl_swap
    (φ : (⊤ : SimpleGraph (Fin 5)).edgeSet → Finset (Fin 4)) (a b : Fin 5) :
    op_1627_not_realizable_parameters_four_three_two_two_pl φ s(a,b) =
      op_1627_not_realizable_parameters_four_three_two_two_pl φ s(b,a) := by
  rw [Sym2.eq_swap]

lemma op_1627_not_realizable_parameters_four_three_two_two_threesingle
    (i j : Fin 4) (hij : i ≠ j) (a : Finset (Fin 4)) (ha : a.card = 3) :
    (if i ∉ a then (1:ℕ) else 0) + (if j ∉ a then (1:ℕ) else 0) +
      (if ({i,j} : Finset (Fin 4)) ⊆ a then 1 else 0) = 1 := by
  by_cases h1 : i ∈ a
  · by_cases h2 : j ∈ a
    · have hsub : ({i,j} : Finset (Fin 4)) ⊆ a := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      simp [h1, h2, hsub]
    · have hsub : ¬ ({i,j} : Finset (Fin 4)) ⊆ a := by
        intro h; exact h2 (h (by simp))
      simp [h1, h2, hsub]
  · by_cases h2 : j ∈ a
    · have hsub : ¬ ({i,j} : Finset (Fin 4)) ⊆ a := by
        intro h; exact h1 (h (by simp))
      simp [h1, h2, hsub]
    · exfalso
      have hdisj : Disjoint a ({i,j} : Finset (Fin 4)) := by
        rw [Finset.disjoint_left]
        intro x hxa hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        exacts [h1 hxa, h2 hxa]
      have hc2 : ({i,j} : Finset (Fin 4)).card = 2 := by simp [hij]
      have := Finset.card_le_card (Finset.subset_univ (a ∪ ({i,j} : Finset (Fin 4))))
      rw [Finset.card_union_of_disjoint hdisj, hc2, Finset.card_univ] at this
      simp at this
      omega

lemma op_1627_not_realizable_parameters_four_three_two_two_tsum_missing
    (N : Multiset (Finset (Fin 4))) (hN : ∀ S ∈ N, S.card = 3) :
    ∑ i : Fin 4, (N.filter (fun S => i ∉ S)).card = N.card := by
  revert hN
  induction N using Multiset.induction with
  | empty => intro hN; simp
  | cons a s ih =>
    intro hN
    have ha : a.card = 3 := hN a (Multiset.mem_cons_self a s)
    have hs : ∀ S ∈ s, S.card = 3 := fun S hS => hN S (Multiset.mem_cons_of_mem hS)
    have ihs := ih hs
    have ihs' : ∑ x : Fin 4, Multiset.countP (fun S => x ∉ S) s = s.card := by
      simpa only [Multiset.countP_eq_card_filter] using ihs
    have hsingle : ∑ i : Fin 4, (if i ∉ a then (1:ℕ) else 0) = 1 := by
      rw [← Finset.card_filter]
      have hh : (Finset.univ.filter (fun i : Fin 4 => i ∉ a)) = Finset.univ \ a := by
        ext i; simp
      rw [hh, Finset.card_sdiff]
      simp [ha]
    simp only [← Multiset.countP_eq_card_filter]
    rw [Finset.sum_congr rfl (fun i _ => Multiset.countP_cons (fun S => i ∉ S) a s)]
    rw [Finset.sum_add_distrib, ihs', hsingle, Multiset.card_cons]

lemma op_1627_not_realizable_parameters_four_three_two_two_tthree
    (N : Multiset (Finset (Fin 4))) (hN : ∀ S ∈ N, S.card = 3)
    (i j : Fin 4) (hij : i ≠ j) :
    (N.filter (fun S => i ∉ S)).card + (N.filter (fun S => j ∉ S)).card +
      (N.filter (fun S => ({i,j} : Finset (Fin 4)) ⊆ S)).card = N.card := by
  revert hN
  induction N using Multiset.induction with
  | empty => intro hN; simp
  | cons a s ih =>
    intro hN
    have ha : a.card = 3 := hN a (Multiset.mem_cons_self a s)
    have hs : ∀ S ∈ s, S.card = 3 := fun S hS => hN S (Multiset.mem_cons_of_mem hS)
    have ihs := ih hs
    have ihs' : Multiset.countP (fun S => i ∉ S) s + Multiset.countP (fun S => j ∉ S) s +
        Multiset.countP (fun S => ({i,j} : Finset (Fin 4)) ⊆ S) s = s.card := by
      simpa only [Multiset.countP_eq_card_filter] using ihs
    have hsingle := op_1627_not_realizable_parameters_four_three_two_two_threesingle i j hij a ha
    simp only [← Multiset.countP_eq_card_filter]
    simp only [Multiset.countP_cons]
    rw [Multiset.card_cons]
    omega

lemma op_1627_not_realizable_parameters_four_three_two_two_tkey
    (a b c d : ℕ) (h : a+b+c+d = 4) (h1 : 2 ≤ a+b) (h2 : 2 ≤ a+c) (h3 : 2 ≤ a+d)
    (h4 : 2 ≤ b+c) (h5 : 2 ≤ b+d) (h6 : 2 ≤ c+d) : a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  omega

lemma op_1627_not_realizable_parameters_four_three_two_two_tloc
    (N : Multiset (Finset (Fin 4))) (hN : ∀ S ∈ N, S.card = 3) (hcard : N.card = 4)
    (hpack : ∀ T : Finset (Fin 4), T.card = 2 → (N.filter (fun S => T ⊆ S)).card ≤ 2) :
    ∀ i : Fin 4, (N.filter (fun S => i ∉ S)).card = 1 := by
  have hpair : ∀ i j : Fin 4, i ≠ j →
      2 ≤ (N.filter (fun S => i ∉ S)).card + (N.filter (fun S => j ∉ S)).card := by
    intro i j hij
    have ht := op_1627_not_realizable_parameters_four_three_two_two_tthree N hN i j hij
    have hp := hpack ({i,j} : Finset (Fin 4)) (by simp [hij])
    omega
  have hsum : (N.filter (fun S => (0:Fin 4) ∉ S)).card + (N.filter (fun S => (1:Fin 4) ∉ S)).card +
      (N.filter (fun S => (2:Fin 4) ∉ S)).card + (N.filter (fun S => (3:Fin 4) ∉ S)).card = 4 := by
    have := op_1627_not_realizable_parameters_four_three_two_two_tsum_missing N hN
    rw [hcard, Fin.sum_univ_four] at this
    exact this
  have key := op_1627_not_realizable_parameters_four_three_two_two_tkey _ _ _ _
    hsum
    (hpair 0 1 (by decide)) (hpair 0 2 (by decide)) (hpair 0 3 (by decide))
    (hpair 1 2 (by decide)) (hpair 1 3 (by decide)) (hpair 2 3 (by decide))
  obtain ⟨h0, h1, h2, h3⟩ := key
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

lemma op_1627_not_realizable_parameters_four_three_two_two_inc_eq
    (φ : (⊤ : SimpleGraph (Fin 5)).edgeSet → Finset (Fin 4)) (v : Fin 5) :
    incident_edge_multiset φ v
      = Multiset.map
          (fun x : {u // u ∈ Finset.univ.erase v} =>
            op_1627_not_realizable_parameters_four_three_two_two_pl φ s(x.1, v))
          (Finset.univ.erase v).attach.val := by
  rw [incident_edge_multiset]
  refine Multiset.map_congr rfl ?_
  intro x _
  exact (op_1627_not_realizable_parameters_four_three_two_two_pl_pos φ _ _).symm

lemma op_1627_not_realizable_parameters_four_three_two_two_inc_card
    (φ : (⊤ : SimpleGraph (Fin 5)).edgeSet → Finset (Fin 4)) (v : Fin 5) :
    (incident_edge_multiset φ v).card = 4 := by
  rw [incident_edge_multiset, Multiset.card_map]
  have : ((Finset.univ.erase v).attach.val).card = ((Finset.univ.erase v).attach).card := rfl
  rw [this, Finset.card_attach]
  simp

lemma op_1627_not_realizable_parameters_four_three_two_two_inc_mem_card
    (φ : (⊤ : SimpleGraph (Fin 5)).edgeSet → Finset (Fin 4)) (v : Fin 5)
    (hϕ : ∀ e : (⊤ : SimpleGraph (Fin 5)).edgeSet, (φ e).card = 3) :
    ∀ S ∈ incident_edge_multiset φ v, S.card = 3 := by
  intro S hS
  rw [incident_edge_multiset] at hS
  obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hS
  exact hϕ _

lemma op_1627_not_realizable_parameters_four_three_two_two_attach_filter_card
    {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.attach.filter (fun x => p x.1)).card = (s.filter p).card := by
  rw [Finset.filter_attach]
  simp

lemma op_1627_not_realizable_parameters_four_three_two_two_inc_filter_card
    (φ : (⊤ : SimpleGraph (Fin 5)).edgeSet → Finset (Fin 4)) (v : Fin 5) (i : Fin 4) :
    ((incident_edge_multiset φ v).filter (fun S => i ∉ S)).card
      = ((Finset.univ.erase v).filter
          (fun u => i ∉ op_1627_not_realizable_parameters_four_three_two_two_pl φ s(u,v))).card := by
  rw [op_1627_not_realizable_parameters_four_three_two_two_inc_eq φ v, Multiset.filter_map,
    Multiset.card_map]
  simp only [Function.comp_apply]
  rw [show ((Finset.univ.erase v).attach.val.filter
              (fun x => i ∉ op_1627_not_realizable_parameters_four_three_two_two_pl φ s(x.1, v))).card
        = ((Finset.univ.erase v).attach.filter
              (fun x => i ∉ op_1627_not_realizable_parameters_four_three_two_two_pl φ s(x.1, v))).card
        from rfl]
  exact op_1627_not_realizable_parameters_four_three_two_two_attach_filter_card
    (Finset.univ.erase v)
    (fun u => i ∉ op_1627_not_realizable_parameters_four_three_two_two_pl φ s(u,v))

lemma op_1627_not_realizable_parameters_four_three_two_two_neighbor_eq
    (φ : (⊤ : SimpleGraph (Fin 5)).edgeSet → Finset (Fin 4)) (i0 : Fin 4) (v : Fin 5) :
    (SimpleGraph.fromRel
        (fun u w : Fin 5 => i0 ∉ op_1627_not_realizable_parameters_four_three_two_two_pl φ s(u,w))).neighborFinset v
      = (Finset.univ.erase v).filter
          (fun u => i0 ∉ op_1627_not_realizable_parameters_four_three_two_two_pl φ s(u,v)) := by
  rw [SimpleGraph.neighborFinset_eq_filter]
  ext u
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, SimpleGraph.fromRel_adj]
  have key : (i0 ∉ op_1627_not_realizable_parameters_four_three_two_two_pl φ s(v,u)) ↔
      (i0 ∉ op_1627_not_realizable_parameters_four_three_two_two_pl φ s(u,v)) := by
    rw [op_1627_not_realizable_parameters_four_three_two_two_pl_swap φ v u]
  rw [key]
  simp only [true_and, and_true]
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨Ne.symm hne, h.elim id id⟩
  · rintro ⟨hne, h⟩
    exact ⟨Ne.symm hne, Or.inl h⟩

/-- For parameters (r, s, t, h) = (4, 3, 2, 2), where D = 4 is even and the unique maximum multiset has all multiplicities equal to 1, no set-coloring of K_5 can realize feasible local packings at every vertex. -/
theorem op_1627_not_realizable_parameters_four_three_two_two :
    ¬ ∃ ϕ : (⊤ : SimpleGraph (Fin 5)).edgeSet → Finset (Fin 4),
      (∀ e, (ϕ e).card = 3) ∧
      ∀ v : Fin 5, is_feasible_packing 4 3 2 2 (incident_edge_multiset ϕ v) := by
  rintro ⟨φ, hϕ, hpack⟩
  have hloc : ∀ v i, ((incident_edge_multiset φ v).filter (fun S => i ∉ S)).card = 1 := by
    intro v i
    exact op_1627_not_realizable_parameters_four_three_two_two_tloc
      (incident_edge_multiset φ v)
      (op_1627_not_realizable_parameters_four_three_two_two_inc_mem_card φ v hϕ)
      (op_1627_not_realizable_parameters_four_three_two_two_inc_card φ v)
      (fun T hT => (hpack v).2 T hT) i
  have hloc' : ∀ v,
      ((Finset.univ.erase v).filter
        (fun u => (0:Fin 4) ∉ op_1627_not_realizable_parameters_four_three_two_two_pl φ s(u,v))).card = 1 := by
    intro v
    rw [← op_1627_not_realizable_parameters_four_three_two_two_inc_filter_card φ v 0]
    exact hloc v 0
  let H : SimpleGraph (Fin 5) := SimpleGraph.fromRel
    (fun u w : Fin 5 => (0:Fin 4) ∉ op_1627_not_realizable_parameters_four_three_two_two_pl φ s(u,w))
  have hdeg : ∀ v, H.degree v = 1 := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      op_1627_not_realizable_parameters_four_three_two_two_neighbor_eq φ 0 v]
    exact hloc' v
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges H
  have hsum' : ∑ v : Fin 5, (1:ℕ) = 2 * H.edgeFinset.card := by
    rw [← hsum]
    exact Finset.sum_congr rfl (fun v _ => (hdeg v).symm)
  simp at hsum'
  omega
