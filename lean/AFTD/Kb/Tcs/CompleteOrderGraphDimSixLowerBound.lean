import AFTD.Prelude
import AFTD.Kb.Tcs.OrderGraph
import AFTD.Kb.Tcs.OrderGraphEdgesGe
import AFTD.Kb.Tcs.Order
import AFTD.Kb.Tcs.OrderGraphTopSet
import AFTD.Kb.Tcs.OrderPos
import AFTD.Kb.Tcs.OrderGraphIsComplete
import AFTD.Kb.Tcs.OrderMoveToFront
import AFTD.Kb.Tcs.OrderGraphServes

/-!
# complete_order_graph_dim_six_lower_bound

Topic: combinatorics   Node: 049c6da3de4f

Provenance: helper lemma. arXiv:2610.39311 Corollary 8 -- Tight Asymptotic Bounds on the Size of Order Graphs

Every complete order graph of dimension 6 has at least 40 edges.
-/

private lemma complete_order_graph_dim_six_lower_bound_order_mem_elems {d : ℕ} (π : Order d)
    (a : Fin d) : a ∈ π.elems := by
  have h : π.elems.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup π.nodup, π.length_eq]
    simp
  rw [← List.mem_toFinset, h]
  exact Finset.mem_univ a

private lemma complete_order_graph_dim_six_lower_bound_omf_elems {d : ℕ} (a : Fin d)
    (π : Order d) : (order_move_to_front a π).elems = a :: π.elems.erase a := by
  unfold order_move_to_front
  rw [dif_pos (complete_order_graph_dim_six_lower_bound_order_mem_elems π a)]

private lemma complete_order_graph_dim_six_lower_bound_chain3_elems {d : ℕ} {a1 a2 : Fin d}
    (h : a1 ≠ a2) (π1 : Order d) :
    (order_move_to_front a2 (order_move_to_front a1 π1)).elems
      = a2 :: a1 :: (π1.elems.erase a1).erase a2 := by
  rw [complete_order_graph_dim_six_lower_bound_omf_elems,
    complete_order_graph_dim_six_lower_bound_omf_elems, List.erase_cons]
  rw [if_neg (by simpa using h)]

private lemma complete_order_graph_dim_six_lower_bound_chain3_take_two {d : ℕ} {a1 a2 : Fin d}
    (h : a1 ≠ a2) (π1 : Order d) :
    (order_move_to_front a2 (order_move_to_front a1 π1)).elems.take 2 = [a2, a1] := by
  rw [complete_order_graph_dim_six_lower_bound_chain3_elems h]
  rfl

private lemma complete_order_graph_dim_six_lower_bound_chain3_get_one {d : ℕ} {a1 a2 : Fin d}
    (h : a1 ≠ a2) (π1 : Order d) :
    (order_move_to_front a2 (order_move_to_front a1 π1)).elems[1]? = some a1 := by
  rw [complete_order_graph_dim_six_lower_bound_chain3_elems h]
  rfl

private lemma complete_order_graph_dim_six_lower_bound_chain3_idxOf_ge {d : ℕ} {a1 a2 a3 : Fin d}
    (h12 : a1 ≠ a2) (h13 : a1 ≠ a3) (h23 : a2 ≠ a3) (π1 : Order d) :
    2 ≤ List.idxOf a3 (order_move_to_front a2 (order_move_to_front a1 π1)).elems := by
  rw [complete_order_graph_dim_six_lower_bound_chain3_elems h12, List.idxOf_cons_ne _ h23,
    List.idxOf_cons_ne _ h13]
  omega

private lemma complete_order_graph_dim_six_lower_bound_nodup_of_toFinset_card {α : Type}
    [DecidableEq α] {l : List α} (h : l.toFinset.card = l.length) : l.Nodup := by
  have := (Multiset.toFinset_card_eq_card_iff_nodup (m := (l : Multiset α))).mp (by simpa using h)
  simpa using this

private lemma complete_order_graph_dim_six_lower_bound_serves_three {G : OrderGraph 6}
    {S : Finset (Fin 6)} {x : Fin 6} (hx : x ∉ S) (hcard : S.card = 2)
    (hserv : order_graph_serves G S x) :
    ∃ e ∈ G.E, 3 ≤ order_pos e.1 e.2 ∧ order_graph_top_set 3 e = insert x S ∧
      (x = e.2 ∨ e.1.elems[1]? = some x) := by
  rcases hserv with ⟨p, hp, hEdges, hChain, hLen, hLabels, hHL⟩
  have hlen3 : p.length = 3 := by rw [hLen, hcard]
  obtain ⟨e1, e2, e3, rfl⟩ := List.length_eq_three.mp hlen3
  have hstep : (e2.1 = order_move_to_front e1.2 e1.1) ∧
      (e3.1 = order_move_to_front e2.2 e2.1) := by simpa [List.IsChain] using hChain
  obtain ⟨hstep12, hstep23⟩ := hstep
  have hmem3 : e3 ∈ G.E := hEdges e3 (by simp)
  have hset : ({e1.2, e2.2, e3.2} : Finset (Fin 6)) = insert x S := by simpa using hLabels
  have hcardU : (insert x S).card = 3 := by
    rw [Finset.card_insert_of_notMem hx, hcard]
  have hnod : ([e1.2, e2.2, e3.2] : List (Fin 6)).Nodup := by
    apply complete_order_graph_dim_six_lower_bound_nodup_of_toFinset_card
    simp [hset, hcardU]
  simp at hnod
  obtain ⟨⟨h12, h13⟩, h23⟩ := hnod
  have hHL' : e1.2 = x ∨ e3.2 = x := by simpa using hHL
  have hpos : 3 ≤ order_pos e3.1 e3.2 := by
    unfold order_pos
    rw [hstep23, hstep12]
    have := complete_order_graph_dim_six_lower_bound_chain3_idxOf_ge h12 h13 h23 e1.1
    omega
  have h1 : order_graph_top_set 3 e3 = insert e3.2 ({e2.2, e1.2} : Finset (Fin 6)) := by
    simp only [order_graph_top_set, Nat.reduceSub, hstep23, hstep12,
      complete_order_graph_dim_six_lower_bound_chain3_take_two h12]
    simp
  have htop : order_graph_top_set 3 e3 = insert x S := by
    rw [h1, ← hset]
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  refine ⟨e3, hmem3, hpos, htop, ?_⟩
  rcases hHL' with h | h
  · right
    rw [hstep23, hstep12, complete_order_graph_dim_six_lower_bound_chain3_get_one h12 e1.1, h]
  · left; exact h.symm

private lemma complete_order_graph_dim_six_lower_bound_mem_edges_ge {G : OrderGraph 6} {m : ℕ}
    {e : Order 6 × Fin 6} :
    e ∈ order_graph_edges_ge G m ↔ e ∈ G.E ∧ m ≤ order_pos e.1 e.2 := by
  simp [order_graph_edges_ge]

private lemma complete_order_graph_dim_six_lower_bound_mem_fiber {G : OrderGraph 6}
    {U : Finset (Fin 6)} {e : Order 6 × Fin 6} :
    e ∈ (order_graph_edges_ge G 3).filter (fun e => order_graph_top_set 3 e = U) ↔
      e ∈ G.E ∧ 3 ≤ order_pos e.1 e.2 ∧ order_graph_top_set 3 e = U := by
  rw [Finset.mem_filter, complete_order_graph_dim_six_lower_bound_mem_edges_ge]
  tauto

private lemma complete_order_graph_dim_six_lower_bound_head_set_card_le_two (e : Order 6 × Fin 6) :
    (insert e.2 (Finset.univ.filter (fun y : Fin 6 => e.1.elems[1]? = some y))).card ≤ 2 := by
  have h1 : (Finset.univ.filter (fun y : Fin 6 => e.1.elems[1]? = some y)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rw [ha] at hb
    exact Option.some.inj hb
  have h2 := Finset.card_insert_le e.2 (Finset.univ.filter (fun y : Fin 6 => e.1.elems[1]? = some y))
  omega

private lemma complete_order_graph_dim_six_lower_bound_fiber_two {G : OrderGraph 6}
    (hG : order_graph_is_complete G) (U : Finset (Fin 6)) (hU : U.card = 3) :
    2 ≤ ((order_graph_edges_ge G 3).filter (fun e => order_graph_top_set 3 e = U)).card := by
  classical
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.mp hU
  have hU3 : ({p, q, r} : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_eq_three]; exact ⟨p, q, r, hpq, hpr, hqr, rfl⟩
  have hserve : ∀ x ∈ ({p, q, r} : Finset (Fin 6)), ∃ e : Order 6 × Fin 6, e ∈ G.E ∧
      3 ≤ order_pos e.1 e.2 ∧ order_graph_top_set 3 e = ({p, q, r} : Finset (Fin 6)) ∧
      (x = e.2 ∨ e.1.elems[1]? = some x) := by
    intro x hx
    have hxnot : x ∉ ({p, q, r} : Finset (Fin 6)).erase x := Finset.notMem_erase x _
    have hcard2 : (({p, q, r} : Finset (Fin 6)).erase x).card = 2 := by
      rw [Finset.card_erase_of_mem hx, hU3]
    obtain ⟨e, he, hpos, htop, hhl⟩ :=
      complete_order_graph_dim_six_lower_bound_serves_three hxnot hcard2 (hG _ x hxnot)
    exact ⟨e, he, hpos, by rwa [Finset.insert_erase hx] at htop, hhl⟩
  obtain ⟨ep, hep_mem, hep_pos, hep_top, hep_hl⟩ := hserve p (by simp)
  obtain ⟨eq, heq_mem, heq_pos, heq_top, heq_hl⟩ := hserve q (by simp)
  obtain ⟨er, her_mem, her_pos, her_top, her_hl⟩ := hserve r (by simp)
  have hFep : ep ∈ (order_graph_edges_ge G 3).filter (fun e => order_graph_top_set 3 e = {p,q,r}) := by
    rw [complete_order_graph_dim_six_lower_bound_mem_fiber]; exact ⟨hep_mem, hep_pos, hep_top⟩
  have hFeq : eq ∈ (order_graph_edges_ge G 3).filter (fun e => order_graph_top_set 3 e = {p,q,r}) := by
    rw [complete_order_graph_dim_six_lower_bound_mem_fiber]; exact ⟨heq_mem, heq_pos, heq_top⟩
  have hFer : er ∈ (order_graph_edges_ge G 3).filter (fun e => order_graph_top_set 3 e = {p,q,r}) := by
    rw [complete_order_graph_dim_six_lower_bound_mem_fiber]; exact ⟨her_mem, her_pos, her_top⟩
  by_contra hcon
  have hcard1 : ((order_graph_edges_ge G 3).filter
      (fun e => order_graph_top_set 3 e = {p,q,r})).card ≤ 1 := by omega
  have hepq : ep = eq := Finset.card_le_one.mp hcard1 ep hFep eq hFeq
  have hepr : ep = er := Finset.card_le_one.mp hcard1 ep hFep er hFer
  let S := insert ep.2 (Finset.univ.filter (fun y : Fin 6 => ep.1.elems[1]? = some y))
  have hpS : p ∈ S := by
    rcases hep_hl with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  have hqS : q ∈ S := by
    rcases heq_hl with h | h
    · exact Finset.mem_insert.mpr (Or.inl (by rw [hepq]; exact h))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by rw [hepq]; exact h⟩))
  have hrS : r ∈ S := by
    rcases her_hl with h | h
    · exact Finset.mem_insert.mpr (Or.inl (by rw [hepr]; exact h))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by rw [hepr]; exact h⟩))
  have hsub : ({p, q, r} : Finset (Fin 6)) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hpS
    · exact hqS
    · exact hrS
  have h3 : 3 ≤ S.card := by
    have := Finset.card_le_card hsub
    rwa [hU3] at this
  have h2 : S.card ≤ 2 := complete_order_graph_dim_six_lower_bound_head_set_card_le_two ep
  omega

/-- Lower bound on the number of edges of a complete order graph of dimension 6. -/
theorem complete_order_graph_dim_six_lower_bound (G : OrderGraph 6)
    (hG : order_graph_is_complete G) : 40 ≤ G.E.card := by
  classical
  let S := Finset.powersetCard 3 (Finset.univ : Finset (Fin 6))
  let F : Finset (Fin 6) → Finset (Order 6 × Fin 6) :=
    fun U => (order_graph_edges_ge G 3).filter (fun e => order_graph_top_set 3 e = U)
  have hdisj : (S : Set (Finset (Fin 6))).PairwiseDisjoint F := by
    intro U _ U' _ hne
    change Disjoint (F U) (F U')
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [F, Finset.mem_filter] at he he'
    exact hne (he.2.symm.trans he'.2)
  have hcard : (S.biUnion F).card = ∑ U ∈ S, (F U).card := Finset.card_biUnion hdisj
  have hsub : S.biUnion F ⊆ order_graph_edges_ge G 3 :=
    Finset.biUnion_subset.mpr (fun U _ => Finset.filter_subset _ _)
  have hfiber : ∀ U ∈ S, 2 ≤ (F U).card := by
    intro U hU
    rw [Finset.mem_powersetCard] at hU
    exact complete_order_graph_dim_six_lower_bound_fiber_two hG U hU.2
  have h2 : (2 : ℕ) * S.card = 40 := by
    simp only [S, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    decide
  have hsum : 40 ≤ ∑ U ∈ S, (F U).card := by
    have h1 : ∑ U ∈ S, 2 ≤ ∑ U ∈ S, (F U).card := Finset.sum_le_sum hfiber
    rw [Finset.sum_const_nat (fun _ _ => rfl)] at h1
    omega
  calc 40 ≤ ∑ U ∈ S, (F U).card := hsum
    _ = (S.biUnion F).card := hcard.symm
    _ ≤ (order_graph_edges_ge G 3).card := Finset.card_le_card hsub
    _ ≤ G.E.card := Finset.card_le_card
        (fun e he => (complete_order_graph_dim_six_lower_bound_mem_edges_ge.mp he).1)
