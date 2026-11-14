import AFTD.Prelude
import AFTD.Kb.Tcs.GraphCliquePartitionOrientedCrossDegreeBound
import AFTD.Kb.Tcs.Graph125ExceptionalColoringArithmetic
import AFTD.Kb.Tcs.Graph125InducedCliqueCrossBound
import AFTD.Kb.Tcs.DigraphThreeColorCrossArcsDeleteVertexSplit

/-!
# graph_125_exceptional_three_clique_cross_bound

Topic: graphs   Node: 06dd464dcfed

Provenance: helper lemma. Exceptional-vertex counting reduction for OP-110; experiment 26134 checks its numerical budget.

For an oriented subdigraph of a graph on 125 vertices, suppose the vertices other than a distinguished vertex form three color classes that are cliques, the graph has the displayed edge and degree bounds, and the distinguished vertex has seven outgoing arcs and is assigned a color containing at least one third of its incident arcs. Under the displayed overlap and indegree inequalities, at most 50 arcs cross the colors.
-/

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem graph_125_exceptional_three_clique_cross_bound
    (G : SimpleGraph (Fin 125)) [DecidableRel G.Adj]
    (D : Digraph (Fin 125)) [DecidableRel D.Adj] (x : Fin 125) (col : Fin 125 → Fin 3)
    (hclique : ∀ u v, u ≠ x → v ≠ x → col u = col v → u ≠ v → G.Adj u v)
    (hsub : ∀ u v, D.Adj u v → G.Adj u v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hout : (Finset.univ.filter fun w => D.Adj x w).card = 7)
    (hedges : G.edgeFinset.card ≤ 2625)
    (hdeg : 46 ≤ G.degree x)
    (hoverlap : 42 ≤ 2625 - G.edgeFinset.card ∧ 2625 - G.edgeFinset.card ≤ 43)
    (hbound : 6 * (Finset.univ.filter fun w => D.Adj w x).card ≤
       G.degree x + (2625 - G.edgeFinset.card))
    (hcap : G.degree x + (2625 - G.edgeFinset.card) ≤ 124)
    (hbalanced : (Finset.univ.filter fun w => D.Adj w x).card + 7 ≤
       3 * (Finset.univ.filter fun w => col w = col x ∧ (D.Adj x w ∨ D.Adj w x)).card) :
    (∑ v : Fin 125, (Finset.univ.filter fun w => col w ≠ col v ∧ D.Adj v w).card) ≤ 50 := by
  classical
  let S : Set (Fin 125) := {x}ᶜ
  let E : Digraph S := ⟨fun u v => D.Adj u.1 v.1⟩
  let rest : ℕ := ∑ u : S, (Finset.univ.filter fun v : S => col v.1 ≠ col u.1 ∧ E.Adj u v).card
  let O : Finset (Fin 125) := Finset.univ.filter fun w => D.Adj x w
  let I : Finset (Fin 125) := Finset.univ.filter fun w => D.Adj w x
  let M := O ∪ I
  let A := M.filter fun w => col w = col x
  let OC := O.filter fun w => col w ≠ col x
  let IC := I.filter fun w => col w ≠ col x
  let t := I.card
  let z := 2625 - G.edgeFinset.card
  let d := G.degree x
  have hdOI : Disjoint O I := by
    apply Finset.disjoint_left.mpr
    intro v hv1 hv2
    exact hori x v (Finset.mem_filter.mp hv1).2 (Finset.mem_filter.mp hv2).2
  have hdC : Disjoint OC IC := by
    apply Finset.disjoint_left.mpr
    intro v hv1 hv2
    exact Finset.disjoint_left.mp hdOI (Finset.mem_filter.mp hv1).1 (Finset.mem_filter.mp hv2).1
  have hM : M.card = 7+t := by
    rw [Finset.card_union_of_disjoint hdOI]
    change O.card = 7 at hout
    omega
  have hsame : (Finset.univ.filter fun w => col w = col x ∧ (D.Adj x w ∨ D.Adj w x)) = A := by
    ext w
    simp only [A,M,O,I, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    tauto
  have hcross : M.filter (fun w => col w ≠ col x) = OC ∪ IC := by
    ext w
    simp only [OC,IC,M,O,I, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    tauto
  have hparts : A.card + OC.card + IC.card = 7+t := by
    have hp := Finset.card_filter_add_card_filter_not (s := M) (fun w => col w = col x)
    change A.card + (M.filter fun w => col w ≠ col x).card = M.card at hp
    rw [hcross, Finset.card_union_of_disjoint hdC,hM] at hp
    omega
  have hb : t+7 ≤ 3*A.card := by
    rw [hsame] at hbalanced
    exact hbalanced
  have hr : rest + 2501 ≤ G.edgeFinset.card - d := by
    have h := graph_125_induced_clique_cross_bound G D x col hclique hsub hori
    exact h
  have hrest : rest ≤ 124-z-d := by omega
  have hnum := graph_125_exceptional_coloring_arithmetic z d t A.card hoverlap.1 hoverlap.2 hdeg hbound hcap hb
  have hs := digraph_three_color_cross_arcs_delete_vertex_split (Fin 125) D x col
  have hsplit : (∑ v : Fin 125, (Finset.univ.filter fun w => col w ≠ col v ∧ D.Adj v w).card) =
      rest + OC.card + IC.card := by
    have ho : (Finset.univ.filter fun w => col w ≠ col x ∧ D.Adj x w) = OC := by
      ext w
      simp [OC,O, and_comm]
    have hi : (Finset.univ.filter fun w => col w ≠ col x ∧ D.Adj w x) = IC := by
      ext w
      simp [IC,I, and_comm]
    rw [ho,hi] at hs
    exact hs
  rw [hsplit]
  omega
