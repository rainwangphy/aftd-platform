import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSafe17Graph
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphSafe17Structure
import AFTD.Kb.Tcs.DigraphSafe17EveryProperCycleUnsafe

/-!
# digraph_safe_cycle_universal_criterion_false

Topic: graphs   Node: 46d32d2445de

Provenance: helper lemma. Safe-cycle obstruction for OP-110; experiment 13260.

It is false that every loopless oriented seven-diregular graph on seventeen vertices with a complete common-predecessor graph contains a proper directed cycle whose deletion costs every remaining vertex at most two outneighbors.
-/

private instance in504_safe17_final_decAdj_6 : DecidableRel digraph_safe17_graph.Adj := by
  intro u v
  unfold digraph_safe17_graph
  infer_instance

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem digraph_safe_cycle_universal_criterion_false :
    ¬ (∀ (D : Digraph (Fin 17)) [DecidableRel D.Adj],
      (∀ u, ¬ D.Adj u u) →
      (∀ u v, D.Adj u v → ¬ D.Adj v u) →
      (∀ u, (Finset.univ.filter fun v => D.Adj u v).card = 7) →
      (∀ v, (Finset.univ.filter fun u => D.Adj u v).card = 7) →
      (∀ u v, u ≠ v → ∃ p, D.Adj p u ∧ D.Adj p v) →
      ∃ C : Finset (Fin 17), C ≠ Finset.univ ∧ digraph_directed_cycle_on D C ∧
        ∀ v ∉ C, (C.filter fun w => D.Adj v w).card ≤ 2) := by
  intro h
  obtain ⟨hloop,hori,hout,hin,hcommon⟩ := digraph_safe17_structure
  obtain ⟨C,hproper,hcycle,hsafe⟩ := h digraph_safe17_graph hloop hori hout hin hcommon
  obtain ⟨v,hv,hthree⟩ := digraph_safe17_every_proper_cycle_unsafe C hcycle hproper
  have htwo := hsafe v hv
  omega
