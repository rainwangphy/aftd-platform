import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPieceThread
import AFTD.Kb.GameTheoryEconomics.IsTreeSpecial
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans
import AFTD.Kb.Tcs.Support

/-!
# arrows_grundy_three_witness_tree_structure

Topic: combinatorial_games   Node: aa82caf6b331

Provenance: helper lemma. step towards subcubic_short_thread_arrows_grundy_three_achievable

The explicit 21-vertex graph defined by 20 edges is a tree of maximum degree at most 3, all of whose piece threads have length at most 3.
-/

/-- The edge list of the 21-vertex witness graph. -/
def arrows_grundy_three_witness_tree_structure_rlist : List (Fin 21 × Fin 21) :=
  [((1 : Fin 21), (0 : Fin 21)), (1, 2), (0, 8), (2, 3), (2, 6), (3, 4), (4, 5), (6, 7), (8, 9), (8, 14), (9, 10), (9, 13), (10, 11), (11, 12), (14, 15), (5, 16), (7, 17), (12, 18), (13, 19), (15, 20)]

/-- The 21-vertex witness graph. -/
def arrows_grundy_three_witness_tree_structure_graph : SimpleGraph (Fin 21) :=
  SimpleGraph.fromRel (fun u v : Fin 21 => (u, v) ∈ arrows_grundy_three_witness_tree_structure_rlist)

instance arrows_grundy_three_witness_tree_structure_decAdj :
    DecidableRel arrows_grundy_three_witness_tree_structure_graph.Adj := by
  intro u v
  unfold arrows_grundy_three_witness_tree_structure_graph SimpleGraph.fromRel
  infer_instance

instance arrows_grundy_three_witness_tree_structure_decSpecial :
    DecidablePred (is_tree_special arrows_grundy_three_witness_tree_structure_graph) := by
  intro v
  unfold is_tree_special
  infer_instance

/-- Vertices at internal walk positions lie in the interior vertex list of the thread. -/
lemma arrows_grundy_three_witness_tree_structure_getVert_mem_interior
    {u v : Fin 21} (p : arrows_grundy_three_witness_tree_structure_graph.Walk u v) {i : ℕ}
    (h1 : 1 ≤ i) (h2 : i < p.length) :
    p.getVert i ∈ (p.support.drop 1).dropLast := by
  rw [List.dropLast_drop_eq_drop_dropLast, List.mem_drop_iff_getElem]
  refine ⟨i - 1, ?_, ?_⟩
  · rw [List.length_dropLast, SimpleGraph.Walk.length_support]; omega
  · rw [List.getElem_dropLast (by rw [List.length_dropLast, SimpleGraph.Walk.length_support]; omega)]
    rw [SimpleGraph.Walk.support_getElem_eq_getVert p (by rw [SimpleGraph.Walk.length_support]; omega)]
    have hidx : 1 + (i - 1) = i := by omega
    rw [hidx]

/-- Locally in the witness graph, a degree-2 non-special vertex has its two neighbours
uniquely determined up to symmetry: no two distinct neighbours of it are both degree-2 and
non-special. -/
lemma arrows_grundy_three_witness_tree_structure_center :
    ∀ (c b d : Fin 21),
      arrows_grundy_three_witness_tree_structure_graph.Adj c b →
      arrows_grundy_three_witness_tree_structure_graph.Adj c d →
      arrows_grundy_three_witness_tree_structure_graph.degree c = 2 →
      ¬ is_tree_special arrows_grundy_three_witness_tree_structure_graph c →
      arrows_grundy_three_witness_tree_structure_graph.degree b = 2 →
      ¬ is_tree_special arrows_grundy_three_witness_tree_structure_graph b →
      arrows_grundy_three_witness_tree_structure_graph.degree d = 2 →
      ¬ is_tree_special arrows_grundy_three_witness_tree_structure_graph d → b = d := by
  decide

/-- Every vertex of the witness graph with positive index has a neighbour of smaller index. -/
lemma arrows_grundy_three_witness_tree_structure_parent :
    ∀ u : Fin 21, 0 < u.val →
      ∃ v : Fin 21, v.val < u.val ∧ arrows_grundy_three_witness_tree_structure_graph.Adj v u := by
  decide

/-- Vertex `0` reaches every vertex of the witness graph. -/
lemma arrows_grundy_three_witness_tree_structure_reachable_zero (u : Fin 21) :
    arrows_grundy_three_witness_tree_structure_graph.Reachable 0 u := by
  suffices h : ∀ n, ∀ u : Fin 21, u.val < n →
      arrows_grundy_three_witness_tree_structure_graph.Reachable 0 u from h 21 u u.isLt
  intro n
  induction n with
  | zero => intro u hu; omega
  | succ n ih =>
      intro u hu
      by_cases h0 : u.val = 0
      · have hu0 : u = 0 := Fin.ext h0
        subst hu0
        exact ⟨SimpleGraph.Walk.nil⟩
      · have hpos : 0 < u.val := Nat.pos_of_ne_zero h0
        obtain ⟨v, hvlt, hvu⟩ := arrows_grundy_three_witness_tree_structure_parent u hpos
        have hvltn : v.val < n := by omega
        exact (ih v hvltn).trans ⟨SimpleGraph.Walk.cons hvu SimpleGraph.Walk.nil⟩

/-- The witness graph is connected. -/
lemma arrows_grundy_three_witness_tree_structure_connected :
    arrows_grundy_three_witness_tree_structure_graph.Connected := by
  refine SimpleGraph.Connected.mk ?_
  intro u v
  exact (arrows_grundy_three_witness_tree_structure_reachable_zero u).symm.trans
    (arrows_grundy_three_witness_tree_structure_reachable_zero v)

/-- The witness graph has 20 edges, one fewer than its number of vertices. -/
lemma arrows_grundy_three_witness_tree_structure_card :
    Nat.card arrows_grundy_three_witness_tree_structure_graph.edgeSet + 1 = Nat.card (Fin 21) := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  decide

/-- The witness graph is a tree. -/
lemma arrows_grundy_three_witness_tree_structure_isTree :
    arrows_grundy_three_witness_tree_structure_graph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  exact ⟨arrows_grundy_three_witness_tree_structure_connected,
    arrows_grundy_three_witness_tree_structure_card⟩

/-- The witness graph has maximum degree at most 3. -/
lemma arrows_grundy_three_witness_tree_structure_maxDegree :
    arrows_grundy_three_witness_tree_structure_graph.maxDegree ≤ 3 := by
  decide

/-- Every piece thread of the witness graph has length at most 3. -/
lemma arrows_grundy_three_witness_tree_structure_thread (u v : Fin 21)
    (p : arrows_grundy_three_witness_tree_structure_graph.Walk u v)
    (hp : is_piece_thread arrows_grundy_three_witness_tree_structure_graph p) :
    p.length ≤ 3 := by
  by_contra h
  have hidx1 : 1 < p.length := by omega
  have hidx2 : 2 < p.length := by omega
  have hidx3 : 3 < p.length := by omega
  have hlen1 : 1 ≤ p.length := by omega
  have hlen3 : 3 ≤ p.length := by omega
  obtain ⟨hd1, hs1⟩ := hp.2.2.2.2 (p.getVert 1)
    (arrows_grundy_three_witness_tree_structure_getVert_mem_interior p (by norm_num) hidx1)
  obtain ⟨hd2, hs2⟩ := hp.2.2.2.2 (p.getVert 2)
    (arrows_grundy_three_witness_tree_structure_getVert_mem_interior p (by norm_num) hidx2)
  obtain ⟨hd3, hs3⟩ := hp.2.2.2.2 (p.getVert 3)
    (arrows_grundy_three_witness_tree_structure_getVert_mem_interior p (by norm_num) hidx3)
  have hadj12 : arrows_grundy_three_witness_tree_structure_graph.Adj (p.getVert 1) (p.getVert 2) :=
    p.adj_getVert_succ hidx1
  have hadj23 : arrows_grundy_three_witness_tree_structure_graph.Adj (p.getVert 2) (p.getVert 3) :=
    p.adj_getVert_succ hidx2
  have heq : p.getVert 1 = p.getVert 3 :=
    arrows_grundy_three_witness_tree_structure_center (p.getVert 2) (p.getVert 1) (p.getVert 3)
      hadj12.symm hadj23 hd2 hs2 hd1 hs1 hd3 hs3
  have hne : p.getVert 1 ≠ p.getVert 3 := by
    intro hc
    have h13 := hp.1.getVert_injOn (by simp [hlen1]) (by simp [hlen3]) hc
    omega
  exact hne heq

/-- The explicit 21-vertex graph defined by 20 edges is a tree of maximum degree at most 3, all of whose piece threads have length at most 3. -/
theorem arrows_grundy_three_witness_tree_structure :
    ∃ (T : SimpleGraph (Fin 21)) (_ : DecidableRel T.Adj),
      T.IsTree ∧
      T.maxDegree ≤ 3 ∧
      (∀ (u v : Fin 21) (p : T.Walk u v), is_piece_thread T p → p.length ≤ 3) ∧
      T = SimpleGraph.fromRel (fun u v : Fin 21 => (u, v) ∈ [((1 : Fin 21), (0 : Fin 21)), (1, 2), (0, 8), (2, 3), (2, 6), (3, 4), (4, 5), (6, 7), (8, 9), (8, 14), (9, 10), (9, 13), (10, 11), (11, 12), (14, 15), (5, 16), (7, 17), (12, 18), (13, 19), (15, 20)]) := by
  refine ⟨arrows_grundy_three_witness_tree_structure_graph,
    arrows_grundy_three_witness_tree_structure_decAdj, ?_, ?_, ?_, ?_⟩
  · exact arrows_grundy_three_witness_tree_structure_isTree
  · exact arrows_grundy_three_witness_tree_structure_maxDegree
  · exact arrows_grundy_three_witness_tree_structure_thread
  · rfl
