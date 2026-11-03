import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSafe17Graph
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphSafe17FourUnsafe
import AFTD.Kb.Tcs.DigraphSafe17ThreeNeighborsNotSafe

/-!
# digraph_safe17_four_cycle_unsafe

Topic: graphs   Node: 093255ca1e9d

Provenance: helper lemma. Safe-cycle obstruction for OP-110; experiment 13260.

No directed four-cycle in the displayed graph is safe for deletion with a two-neighbor budget.
-/

private instance in504_safe17_final_decAdj_4 : DecidableRel digraph_safe17_graph.Adj := by
  intro u v
  unfold digraph_safe17_graph
  infer_instance

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem digraph_safe17_four_cycle_unsafe
    (C : Finset (Fin 17)) (hcycle : digraph_directed_cycle_on digraph_safe17_graph C)
    (hcard : C.card = 4)
    (hsafe : ∀ x ∉ C, (C.filter fun w => digraph_safe17_graph.Adj x w).card ≤ 2) : False := by
  classical
  obtain ⟨l,hn,hlen0,hset,hchain,hclose⟩ := hcycle
  have hlen : l.length = 4 := by
    have h := List.toFinset_card_of_nodup hn
    rw [hset,hcard] at h
    omega
  have hshape : ∃ u a b c, l = [u,a,b,c] := by
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
          | nil => simp at hlen
          | cons c l =>
            cases l with
            | nil => exact ⟨u,a,b,c,rfl⟩
            | cons d l => simp at hlen
  obtain ⟨u,a,b,c,rfl⟩ := hshape
  have hcset : ({u,a,b,c} : Finset (Fin 17)) = C := by simpa using hset
  have hchain' : digraph_safe17_graph.Adj u a ∧ digraph_safe17_graph.Adj a b ∧
      digraph_safe17_graph.Adj b c := by simpa [List.isChain_cons_cons] using hchain
  have hcu : digraph_safe17_graph.Adj c u := by
    obtain ⟨x,y,hx,hy,hxy⟩ := hclose
    simp only [List.head?_cons, Option.some.injEq] at hx
    simp at hy
    subst x
    subst y
    exact hxy
  have hd : u ≠ a ∧ u ≠ b ∧ u ≠ c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by simpa [and_assoc] using hn
  obtain ⟨v,hvu,hva,hvb,hvc,htrip⟩ :=
    digraph_safe17_four_unsafe u a b c hchain'.1 hchain'.2.1 hchain'.2.2 hcu
  have hv : v ∉ C := by rw [← hcset]; simp [hvu,hva,hvb,hvc]
  have huC : u ∈ C := by rw [← hcset]; simp
  have haC : a ∈ C := by rw [← hcset]; simp
  have hbC : b ∈ C := by rw [← hcset]; simp
  have hcC : c ∈ C := by rw [← hcset]; simp
  rcases htrip with h | h | h | h
  · exact digraph_safe17_three_neighbors_not_safe C v u a b hv hd.1 hd.2.1 hd.2.2.2.1 huC haC hbC h.1 h.2.1 h.2.2 hsafe
  · exact digraph_safe17_three_neighbors_not_safe C v u a c hv hd.1 hd.2.2.1 hd.2.2.2.2.1 huC haC hcC h.1 h.2.1 h.2.2 hsafe
  · exact digraph_safe17_three_neighbors_not_safe C v u b c hv hd.2.1 hd.2.2.1 hd.2.2.2.2.2 huC hbC hcC h.1 h.2.1 h.2.2 hsafe
  · exact digraph_safe17_three_neighbors_not_safe C v a b c hv hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2 haC hbC hcC h.1 h.2.1 h.2.2 hsafe
