import AFTD.Prelude
import AFTD.Kb.Tcs.Op874pfEdges

/-!
# op874_pseudoforest_graph_and_cut_public

Topic: graphs   Node: 7294a8254993

Provenance: helper lemma. OP-874: graph and matching-cut certificate for the pseudoforest obstruction.

The explicit eight-vertex graph is connected, bridgeless and cubic, and has the displayed perfect matching, two factor squares and a locally maximal matching cut of globally maximum score six.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

private def op874pfg_matching : Finset (Sym2 (Fin 8)) :=
  {s(0,5),s(2,6),s(1,7),s(3,4)}
private def op874pfg_factor : Finset (Sym2 (Fin 8)) :=
  {s(0,1),s(1,2),s(2,3),s(3,0),s(4,5),s(5,6),s(6,7),s(7,4)}
private def op874pfg_all_edges : Finset (Sym2 (Fin 8)) := op874pf_edges
private def op874pfg_graph : SimpleGraph (Fin 8) where
  Adj u v := u ≠ v ∧ s(u,v) ∈ op874pfg_matching ∪ op874pfg_factor
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, by simpa [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩
private instance : DecidableRel op874pfg_graph.Adj := fun u v => by
  change Decidable (u ≠ v ∧ s(u,v) ∈ op874pfg_matching ∪ op874pfg_factor)
  infer_instance
private def op874pfg_bits : Fin 8 → Bool := ![true,true,false,false,false,true,false,true]
private def op874pfg_mate : Fin 8 → Fin 8 := ![5,7,6,4,3,0,2,1]
private def op874pfg_same (v : Fin 8) : ℕ :=
  (Finset.univ.filter fun w : Fin 8 =>
    s(v,w) ∈ op874pfg_factor ∧ op874pfg_bits v = op874pfg_bits w).card
private def op874pfg_score (b : Fin 8 → Bool) : ℕ :=
  ([(0,1),(1,2),(2,3),(3,0),(4,5),(5,6),(6,7),(7,4)] : List (Fin 8 × Fin 8)).filter
    (fun e => b e.1 != b e.2) |>.length

private theorem op874pfg_connected : op874pfg_graph.Connected := by decide
private theorem op874pfg_avoid_edge : ∀ u v : Fin 8,
    (op874pfg_graph.deleteEdges {s(u,v)}).Reachable u v := by
  intro u
  fin_cases u <;> decide
private theorem op874pfg_bridgeless : ∀ e : Sym2 (Fin 8), ¬ op874pfg_graph.IsBridge e := by
  intro e
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.isBridge_iff, not_not]
    exact op874pfg_avoid_edge u v

theorem op874_pseudoforest_graph_and_cut_public :
    let M : Finset (Sym2 (Fin 8)) := {s(0,5),s(2,6),s(1,7),s(3,4)}
    let F : Finset (Sym2 (Fin 8)) := {s(0,1),s(1,2),s(2,3),s(3,0),s(4,5),s(5,6),s(6,7),s(7,4)}
    let b : Fin 8 → Bool := ![true,true,false,false,false,true,false,true]
    let mate : Fin 8 → Fin 8 := ![5,7,6,4,3,0,2,1]
    let same := fun v : Fin 8 => (Finset.univ.filter fun w : Fin 8 =>
      s(v,w) ∈ F ∧ b v = b w).card
    let score := fun c : Fin 8 → Bool =>
      (([(0,1),(1,2),(2,3),(3,0),(4,5),(5,6),(6,7),(7,4)] : List (Fin 8 × Fin 8)).filter
        fun e => c e.1 != c e.2).length
    ∃ G : SimpleGraph (Fin 8), G.Connected ∧
      (∀ e : Sym2 (Fin 8), ¬ G.IsBridge e) ∧
      (∀ u v, G.Adj u v ↔ u ≠ v ∧ s(u,v) ∈ op874pf_edges) ∧
      (∀ v : Fin 8, (op874pf_edges.filter fun e => v ∈ e).card=3) ∧
      Disjoint M F ∧ (∀ v : Fin 8, (M.filter fun e => v ∈ e).card=1) ∧
      (∀ v : Fin 8, mate (mate v) = v ∧ mate v ≠ v ∧ s(v,mate v) ∈ M ∧
        b v = b (mate v) ∧ same v + same (mate v) ≤ 2) ∧
      score b = 6 ∧
      (∀ c : Fin 8 → Bool,
        c 0=c 5 → c 1=c 7 → c 2=c 6 → c 3=c 4 → score c ≤ 6) := by
  refine ⟨op874pfg_graph, op874pfg_connected, op874pfg_bridgeless, ?_, by decide,
    by decide, by decide, by decide, by decide, by decide⟩
  have hE : op874pf_edges = op874pfg_matching ∪ op874pfg_factor := by decide
  intro u v
  change (u ≠ v ∧ s(u,v) ∈ op874pfg_matching ∪ op874pfg_factor) ↔
    (u ≠ v ∧ s(u,v) ∈ op874pf_edges)
  rw [hE]
