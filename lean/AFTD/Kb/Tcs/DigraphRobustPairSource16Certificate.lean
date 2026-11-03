import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphRobustPairSource16Graph
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph

/-!
# digraph_robust_pair_source16_certificate

Topic: graphs   Node: 7852e20a3147

Provenance: helper lemma. Finite pair-deletion obstruction for the four-cycle campaign; experiments 13432 and 13435.

The explicit sixteen-vertex graph is loopless and oriented, has minimum outdegree seven and auxiliary independence at most two, and has four disjoint directed cycles. For any two disjoint directed cycles, an outside vertex has at least six out-neighbors in their union.
-/

private instance : DecidableRel digraph_robust_pair_source16_graph.Adj := by
  intro u v
  unfold digraph_robust_pair_source16_graph
  infer_instance

private theorem in516_apex_orientation :
    ∀ u v, digraph_robust_pair_source16_graph.Adj u v → ¬ digraph_robust_pair_source16_graph.Adj v u := by
  decide

private theorem in516_apex_indeg_zero : ∀ v, ¬ digraph_robust_pair_source16_graph.Adj v 15 := by
  decide

private theorem in516_apex_cycles_avoid (C : Finset (Fin 16))
    (hC : digraph_directed_cycle_on digraph_robust_pair_source16_graph C) : 15 ∉ C := by
  obtain ⟨l, hnodup, hlen, hset, hchain, a, b, hhead, hlast, hclose⟩ := hC
  cases l with
  | nil => simp at hlen
  | cons x xs =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst a
    have hx : x ≠ 15 := by
      intro h
      subst x
      exact in516_apex_indeg_zero b hclose
    have hall : ∀ y ∈ x :: xs, y ≠ 15 := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hchain.cons_induction (fun z => z ≠ 15) xs (by
          intro u v huv _ hve
          subst v
          exact in516_apex_indeg_zero u huv) hx y hy
    intro h
    rw [← hset, List.mem_toFinset] at h
    exact hall 15 h rfl

private theorem in516_apex_cycle_card (C : Finset (Fin 16))
    (hC : digraph_directed_cycle_on digraph_robust_pair_source16_graph C) : 3 ≤ C.card := by
  obtain ⟨l, hnodup, hlen, hset, hchain, a, b, hhead, hlast, hclose⟩ := hC
  have hcard := List.toFinset_card_of_nodup hnodup
  rw [hset] at hcard
  by_contra h
  have htwo : l.length = 2 := by omega
  cases l with
  | nil => simp at htwo
  | cons u l =>
    cases l with
    | nil => simp at htwo
    | cons v l =>
      cases l with
      | cons w l => simp at htwo
      | nil =>
        have huv : digraph_robust_pair_source16_graph.Adj u v := by simpa [List.isChain_cons_cons] using hchain
        have hvu : digraph_robust_pair_source16_graph.Adj v u := by
          simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hhead hlast
          subst a
          subst b
          exact hclose
        exact (in516_apex_orientation u v huv) hvu

private theorem in516_apex_triangle (a b c : Fin 16)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : digraph_robust_pair_source16_graph.Adj a b) (h2 : digraph_robust_pair_source16_graph.Adj b c)
    (h3 : digraph_robust_pair_source16_graph.Adj c a) :
    digraph_directed_cycle_on digraph_robust_pair_source16_graph ({a,b,c} : Finset (Fin 16)) := by
  refine ⟨[a,b,c], ?_, by simp, by simp, ?_, ?_⟩
  · simp [hab,hac,hbc]
  · simpa [List.isChain_cons_cons] using ⟨h1,h2⟩
  · exact ⟨a,c,by simp,by simp,h3⟩

private theorem in516_apex_counterexample :
    (∀ v, 7 ≤ (Finset.univ.filter fun w => digraph_robust_pair_source16_graph.Adj v w).card) ∧
    (∃ s : Fin 4 → Finset (Fin 16),
      (∀ i, digraph_directed_cycle_on digraph_robust_pair_source16_graph (s i)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j))) ∧
    (∀ A B : Finset (Fin 16), digraph_directed_cycle_on digraph_robust_pair_source16_graph A →
      digraph_directed_cycle_on digraph_robust_pair_source16_graph B → Disjoint A B →
      ∃ v ∉ A ∪ B, 6 ≤ ((A ∪ B).filter fun w => digraph_robust_pair_source16_graph.Adj v w).card) := by
  classical
  refine ⟨by decide, ?_, ?_⟩
  · let s : Fin 4 → Finset (Fin 16) := ![{0,1,8}, {2,3,10}, {4,5,12}, {6,7,14}]
    refine ⟨s, ?_, ?_⟩
    · intro i
      fin_cases i <;> apply in516_apex_triangle <;> decide
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [s, Finset.disjoint_left]
  · intro A B hA hB hd
    have ha := in516_apex_cycles_avoid A hA
    have hb := in516_apex_cycles_avoid B hB
    have hcard : 6 ≤ (A ∪ B).card := by
      rw [Finset.card_union_of_disjoint hd]
      have h1 := in516_apex_cycle_card A hA
      have h2 := in516_apex_cycle_card B hB
      omega
    refine ⟨15, by simp [ha,hb], ?_⟩
    have hf : (A ∪ B).filter (fun w => digraph_robust_pair_source16_graph.Adj 15 w) = A ∪ B := by
      apply Finset.filter_true_of_mem
      intro w hw
      have hwne : w ≠ 15 := by
        intro hw
        subst w
        exact (Finset.mem_union.mp hw).elim ha hb
      simp [digraph_robust_pair_source16_graph,hwne]
    rw [hf]
    omega

-- The universal source makes all other vertices a clique in the auxiliary graph.
private theorem in516_apex_aux_independence :
    (digraph_common_predecessor_graph digraph_robust_pair_source16_graph).IndepSetFree 3 := by
  classical
  intro S hS
  have hcard : (S.erase 15).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra hab
    have ha' := Finset.mem_erase.mp ha
    have hb' := Finset.mem_erase.mp hb
    have hpa : digraph_robust_pair_source16_graph.Adj 15 a := by simp [digraph_robust_pair_source16_graph, ha'.1]
    have hpb : digraph_robust_pair_source16_graph.Adj 15 b := by simp [digraph_robust_pair_source16_graph, hb'.1]
    exact hS.isIndepSet ha'.2 hb'.2 hab ⟨hab,15,hpa,hpb⟩
  by_cases hm : (15 : Fin 16) ∈ S
  · have hc := Finset.card_erase_of_mem hm
    have hs := hS.card_eq
    omega
  · have he : S.erase 15 = S := Finset.erase_eq_of_notMem hm
    rw [he] at hcard
    have hs := hS.card_eq
    omega

theorem digraph_robust_pair_source16_certificate :
    (∀ v, ¬ digraph_robust_pair_source16_graph.Adj v v) ∧
    (∀ u v, digraph_robust_pair_source16_graph.Adj u v → ¬ digraph_robust_pair_source16_graph.Adj v u) ∧
    (∀ v, 7 ≤ (Finset.univ.filter fun w => digraph_robust_pair_source16_graph.Adj v w).card) ∧
    (digraph_common_predecessor_graph digraph_robust_pair_source16_graph).IndepSetFree 3 ∧
    (∃ s : Fin 4 → Finset (Fin 16),
      (∀ i, digraph_directed_cycle_on digraph_robust_pair_source16_graph (s i)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j))) ∧
    (∀ A B : Finset (Fin 16), digraph_directed_cycle_on digraph_robust_pair_source16_graph A →
      digraph_directed_cycle_on digraph_robust_pair_source16_graph B → Disjoint A B →
      ∃ v ∉ A ∪ B, 6 ≤ ((A ∪ B).filter fun w => digraph_robust_pair_source16_graph.Adj v w).card) := by
  have h := in516_apex_counterexample
  refine ⟨?_, in516_apex_orientation, h.1, in516_apex_aux_independence, h.2.1, h.2.2⟩
  decide
