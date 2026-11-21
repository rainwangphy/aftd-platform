import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable
import AFTD.Kb.Tcs.PerfectMatchingOfAdjacencyInvolution
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# boundary_five_seven_example_edge_essential

Topic: graphs   Node: de3b066f47ac

Provenance: helper lemma. OP-1957: forced nonbridge cross-edge obstruction; experiments 37140 and 37142.

In the explicitly defined 28-vertex four-block graph, the edge from 0 to 14 is present and the graph obtained by deleting it is not 7-extendible.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def in1122_fiveseven_block (v : Fin 28) : ℕ :=
  if v.val < 5 then 0 else if v.val < 14 then 1 else if v.val < 21 then 2 else 3

def in1122_fiveseven_edge (u v : Fin 28) : Prop :=
  u ≠ v ∧
  (in1122_fiveseven_block u = in1122_fiveseven_block v ∨ ((u.val < 14) ≠ (v.val < 14))) ∧
  (min u.val v.val, max u.val v.val) ∉
    ([(14,15),(14,16),(15,16),(0,15),(0,16),(5,14),(5,15),(5,16)] : List (ℕ × ℕ))

instance : DecidableRel in1122_fiveseven_edge := fun _ _ => by
  unfold in1122_fiveseven_edge in1122_fiveseven_block
  infer_instance

def in1122_fiveseven_graph : SimpleGraph (Fin 28) where
  Adj := in1122_fiveseven_edge
  symm := by
    constructor
    intro u v h
    rcases h with ⟨hne, hs, he⟩
    refine ⟨hne.symm, ?_, ?_⟩
    · rcases hs with h | h
      · exact Or.inl h.symm
      · exact Or.inr (Ne.symm h)
    · simpa [min_comm, max_comm] using he
  loopless := by constructor; intro u h; exact h.1 rfl

instance : DecidableRel in1122_fiveseven_graph.Adj :=
  inferInstanceAs (DecidableRel in1122_fiveseven_edge)

def in1122_fiveseven_residual : Finset (Fin 28) :=
  {0,1,2,5,14,15,16,21,22,23,24,25,26,27}

def in1122_fiveseven_mate : Fin 28 → Fin 28 :=
  ![0,1,2,20,19,5,18,17,13,12,11,10,9,8,14,15,16,7,6,4,3,21,22,23,24,25,26,27]

def in1122_fiveseven_residual_mate : Fin 28 → Fin 28 :=
  ![14,16,15,3,4,24,6,7,8,9,10,11,12,13,0,2,1,17,18,19,20,23,27,21,5,26,25,22]

theorem in1122_fiveseven_residual_matching :
    ∃ P : (in1122_fiveseven_graph.induce {v | v ∈ in1122_fiveseven_residual}).Subgraph,
      P.IsPerfectMatching := by
  let R := {v : Fin 28 | v ∈ in1122_fiveseven_residual}
  let f (v : R) : R := ⟨in1122_fiveseven_residual_mate v.val, by revert v; decide⟩
  have hi : Function.Involutive f := by intro v; revert v; decide
  have ha : ∀ v : R, (in1122_fiveseven_graph.induce R).Adj v (f v) := by
    intro v; revert v; decide
  exact perfect_matching_of_adjacency_involution _ f hi ha

theorem in1122_fiveseven_min_degree :
    ∀ v, 16 ≤ (in1122_fiveseven_graph.neighborFinset v).card := by
  decide

theorem in1122_fiveseven_nonbridge :
    ((in1122_fiveseven_graph.induce {v | v ∈ in1122_fiveseven_residual}).deleteEdges
      {s(⟨0,by decide⟩,⟨14,by decide⟩)}).Reachable ⟨0,by decide⟩ ⟨14,by decide⟩ := by
  let H := (in1122_fiveseven_graph.induce {v | v ∈ in1122_fiveseven_residual}).deleteEdges
      {s(⟨0,by decide⟩,⟨14,by decide⟩)}
  have h01 : H.Adj ⟨0,by decide⟩ ⟨1,by decide⟩ := by decide
  have h1y : H.Adj ⟨1,by decide⟩ ⟨14,by decide⟩ := by decide
  exact h01.reachable.trans h1y.reachable

theorem in1122_fiveseven_no_residual_matching :
    ¬ ∃ P : ((in1122_fiveseven_graph.induce {v | v ∈ in1122_fiveseven_residual}).deleteEdges
      {s(⟨0,by decide⟩,⟨14,by decide⟩)}).Subgraph, P.IsPerfectMatching := by
  classical
  let H := (in1122_fiveseven_graph.induce {v | v ∈ in1122_fiveseven_residual}).deleteEdges
      {s(⟨0,by decide⟩,⟨14,by decide⟩)}
  let a : {v : Fin 28 // v ∈ in1122_fiveseven_residual} := ⟨14,by decide⟩
  let b : {v : Fin 28 // v ∈ in1122_fiveseven_residual} := ⟨15,by decide⟩
  let c : {v : Fin 28 // v ∈ in1122_fiveseven_residual} := ⟨16,by decide⟩
  have hallowed : ∀ u : {v : Fin 28 // v ∈ in1122_fiveseven_residual},
      (u.val=14 ∨ u.val=15 ∨ u.val=16) →
      ∀ w, H.Adj u w → w.val.val=1 ∨ w.val.val=2 := by decide
  rintro ⟨P,hP⟩
  obtain ⟨p,hap,-⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP) a
  obtain ⟨q,hbq,-⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP) b
  obtain ⟨r,hcr,-⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP) c
  have hdistinct {u v p q : {v : Fin 28 // v ∈ in1122_fiveseven_residual}}
      (hne : u ≠ v) (hp : P.Adj u p) (hq : P.Adj v q) : p.val.val ≠ q.val.val := by
    intro heq
    have hpq : p=q := Subtype.ext (Fin.ext heq)
    subst q
    exact hne (hP.1.eq_of_adj_left hp.symm hq.symm)
  have hpq := hdistinct (u:=a) (v:=b) (by decide) hap hbq
  have hpr := hdistinct (u:=a) (v:=c) (by decide) hap hcr
  have hqr := hdistinct (u:=b) (v:=c) (by decide) hbq hcr
  have hp := hallowed a (by simp [a]) p (P.adj_sub hap)
  have hq := hallowed b (by simp [b]) q (P.adj_sub hbq)
  have hr := hallowed c (by simp [c]) r (P.adj_sub hcr)
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> rcases hr with hr | hr <;> omega

theorem boundary_five_seven_example_edge_essential :
    in1122_fiveseven_graph.Adj 0 14 ∧
      ¬ is_k_extendable (in1122_fiveseven_graph.deleteEdges {s(0,14)}) 7 := by
  classical
  constructor
  · decide
  · intro hext
    let Z := in1122_fiveseven_graph.deleteEdges {s(0,14)}
    let Q : Set (Fin 28) := {v | v ∉ in1122_fiveseven_residual}
    let fQ (v : Q) : Q := ⟨in1122_fiveseven_mate v.val, by revert v; decide⟩
    have hinv : Function.Involutive fQ := by intro v; revert v; decide
    have hadj : ∀ v : Q, (Z.induce Q).Adj v (fQ v) := by intro v; revert v; decide
    have hQ : ∃ P : (Z.induce Q).Subgraph, P.IsPerfectMatching :=
      perfect_matching_of_adjacency_involution _ fQ hinv hadj
    have hsize : Q.ncard=2*7 := by
      have heq : Q = ↑(Finset.univ \ in1122_fiveseven_residual) := by ext v; simp [Q]
      rw [heq, Set.ncard_coe_finset]
      decide
    have hPM := extendible_matchable_two_k_vertices_complement_matchable Z 7 hext Q hsize hQ
    have heq : Qᶜ = {v | v ∈ in1122_fiveseven_residual} := by ext v; simp [Q]
    rw [heq] at hPM
    -- Deleting an ambient edge and inducing commute.
    apply in1122_fiveseven_no_residual_matching
    have hgraph : Z.induce {v | v ∈ in1122_fiveseven_residual} =
        (in1122_fiveseven_graph.induce {v | v ∈ in1122_fiveseven_residual}).deleteEdges
          {s(⟨0,by decide⟩,⟨14,by decide⟩)} := by
      ext u v
      simp [Z, SimpleGraph.deleteEdges_adj, Subtype.ext_iff]
    rw [← hgraph]
    exact hPM
