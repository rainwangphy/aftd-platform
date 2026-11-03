import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSafe17Graph
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphSafe17TriangleUnsafe
import AFTD.Kb.Tcs.DigraphSafe17ThreeNeighborsNotSafe

/-!
# digraph_safe17_triangle_cycle_unsafe

Topic: graphs   Node: 538ce6fe7193

Provenance: helper lemma. Safe-cycle obstruction for OP-110; experiment 13260.

No directed triangle in the displayed graph is safe for deletion with a two-neighbor budget.
-/

private instance in504_safe17_final_decAdj_2 : DecidableRel digraph_safe17_graph.Adj := by
  intro u v
  unfold digraph_safe17_graph
  infer_instance

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem digraph_safe17_triangle_cycle_unsafe
    (C : Finset (Fin 17)) (hcycle : digraph_directed_cycle_on digraph_safe17_graph C)
    (hcard : C.card = 3)
    (hsafe : ∀ x ∉ C, (C.filter fun w => digraph_safe17_graph.Adj x w).card ≤ 2) : False := by
  classical
  obtain ⟨l,hn,hlen0,hset,hchain,hclose⟩ := hcycle
  have hlen : l.length = 3 := by
    have h := List.toFinset_card_of_nodup hn
    rw [hset,hcard] at h
    omega
  have hshape : ∃ u a b, l = [u,a,b] := by
    cases l with
    | nil => simp at hlen
    | cons u l =>
      cases l with
      | nil => simp at hlen
      | cons a l =>
        cases l with
        | nil => simp at hlen
        | cons b l =>
          cases l with
          | nil => exact ⟨u,a,b,rfl⟩
          | cons c l => simp at hlen
  obtain ⟨u,a,b,rfl⟩ := hshape
  have hcset : ({u,a,b} : Finset (Fin 17)) = C := by simpa using hset
  have hchain' : digraph_safe17_graph.Adj u a ∧ digraph_safe17_graph.Adj a b := by
    simpa [List.isChain_cons_cons] using hchain
  have hbu : digraph_safe17_graph.Adj b u := by
    obtain ⟨x,y,hx,hy,hxy⟩ := hclose
    simp only [List.head?_cons, Option.some.injEq] at hx
    simp at hy
    subst x
    subst y
    exact hxy
  have hdistinct : u ≠ a ∧ u ≠ b ∧ a ≠ b := by simpa [and_assoc] using hn
  obtain ⟨v,hvu,hva,hvb,hv0,hv1,hv2⟩ :=
    digraph_safe17_triangle_unsafe u a b hchain'.1 hchain'.2 hbu
  have hv : v ∉ C := by rw [← hcset]; simp [hvu,hva,hvb]
  apply digraph_safe17_three_neighbors_not_safe C v u a b hv hdistinct.1 hdistinct.2.1 hdistinct.2.2
  · rw [← hcset]; simp
  · rw [← hcset]; simp
  · rw [← hcset]; simp
  · exact hv0
  · exact hv1
  · exact hv2
  · exact hsafe
