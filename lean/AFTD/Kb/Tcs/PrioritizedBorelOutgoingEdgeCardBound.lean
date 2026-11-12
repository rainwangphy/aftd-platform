import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.TreeGameEdge

/-!
# prioritized_borel_outgoing_edge_card_bound

Topic: automata   Node: 59c57c4a4c8d

Provenance: helper lemma. Finite branching bound for arXiv:2611.10136, Conjecture 19.

At any fixed position in a finite-state game with k priorities there are at most 2k times the number of states legal outgoing edges.
-/

theorem prioritized_borel_outgoing_edge_card_bound {Q : Type} [Fintype Q] {k : ℕ}
    (G : PrioritizedBorelGame Q k) (v : List Bool) (q : Q) :
    Set.ncard {e : TreeGameEdge Q k | e ∈ G.edges ∧ e.source_node = v ∧ e.source_state = q} ≤
      2 * k * Fintype.card Q := by
  classical
  let S : Set (TreeGameEdge Q k) :=
    {e | e ∈ G.edges ∧ e.source_node = v ∧ e.source_state = q}
  let code : TreeGameEdge Q k → Bool × Fin k × Q := fun e => (e.dir, e.prio, e.target_state)
  have hinj : Set.InjOn code S := by
    intro e he e' he' hc
    have hv : e.source_node = e'.source_node := he.2.1.trans he'.2.1.symm
    have hq : e.source_state = e'.source_state := he.2.2.trans he'.2.2.symm
    have hd : e.dir = e'.dir := congrArg Prod.fst hc
    have hp : e.prio = e'.prio := congrArg (fun x => x.2.1) hc
    have ht : e.target_state = e'.target_state := congrArg (fun x => x.2.2) hc
    cases e with
    | mk v1 q1 d1 p1 t1 =>
      cases e' with
      | mk v2 q2 d2 p2 t2 =>
        simp only at hv hq hd hp ht
        cases hv; cases hq; cases hd; cases hp; cases ht
        rfl
  have hc := Set.ncard_le_ncard_of_injOn code (s := S) (t := Set.univ)
    (by intro e he; exact Set.mem_univ _) hinj (Set.toFinite _)
  simpa [S, code, Fintype.card_prod, Nat.mul_assoc] using hc
