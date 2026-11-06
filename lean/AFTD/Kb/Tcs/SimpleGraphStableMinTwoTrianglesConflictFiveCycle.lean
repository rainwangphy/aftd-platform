import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamily
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# simple_graph_stable_min_two_triangles_conflict_five_cycle

Topic: graphs   Node: d45ea5097b1b

Provenance: helper lemma. Counterexample to the bipartite-conflict shortcut even in the stable minimum-two-triangles residual; experiments 16600 and 16601.

There is an 11-vertex graph with a maximum packing of five edge-disjoint triangles, every graph edge omitted by some maximum packing and contained in at least two and at most eight triangles, such that the graph stays connected after deletion of any two vertices, and a marking of one edge per packed triangle including every singleton-forced edge has a five-cycle in its unmarked conflict graph.
-/

def tri583_adjB (a b : Fin 11) : Bool :=
  a ≠ b && (a.val = 10 || b.val = 10 ||
    [(0,5),(0,7),(0,8),(1,6),(1,8),(1,9),(2,7),(3,8),(4,9),(7,9),(0,2),(1,3),(4,7),(5,8),(6,9)].any
      (fun p => (p.1 = a.val && p.2 = b.val) || (p.1 = b.val && p.2 = a.val)))

def tri583_G : SimpleGraph (Fin 11) := SimpleGraph.fromRel (fun a b => tri583_adjB a b = true)

instance tri583_G_decidableAdj : DecidableRel tri583_G.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ (tri583_adjB a b = true ∨ tri583_adjB b a = true)))


def tri583_tris : List (Fin 11 × Fin 11 × Fin 11) :=
  [(0,5,8),(5,8,10),(0,8,10),(0,5,10),(1,6,9),(6,9,10),(1,9,10),(1,6,10),(4,7,9),(4,7,10),
   (7,9,10),(4,9,10),(1,3,8),(1,3,10),(3,8,10),(1,8,10),(0,2,7),(0,2,10),(2,7,10),(0,7,10)]

def tri583_Fl : List (Finset (Sym2 (Fin 11))) :=
  tri583_tris.map (fun t => ({s(t.1, t.2.1), s(t.1, t.2.2), s(t.2.1, t.2.2)} : Finset (Sym2 (Fin 11))))

def tri583_Fexp : Finset (Finset (Sym2 (Fin 11))) := tri583_Fl.toFinset

def tri583_Pl : List (Finset (Sym2 (Fin 11))) := [{s(0, 2), s(0, 10), s(2, 10)}, {s(1, 3), s(1, 10), s(3, 10)}, {s(4, 7), s(4, 10), s(7, 10)}, {s(5, 8), s(5, 10), s(8, 10)}, {s(6, 9), s(6, 10), s(9, 10)}]

def tri583_P : Finset (Finset (Sym2 (Fin 11))) := tri583_Pl.toFinset

def tri583_Cl : List (List (Finset (Sym2 (Fin 11)))) :=
  [[{s(0, 2), s(0, 7), s(2, 7)}, {s(0, 5), s(0, 8), s(5, 8)}, {s(1, 3), s(1, 8), s(3, 8)}, {s(1, 6), s(1, 9), s(6, 9)}, {s(4, 7), s(4, 9), s(7, 9)}],
   [{s(0, 2), s(0, 10), s(2, 10)}, {s(1, 3), s(1, 10), s(3, 10)}, {s(4, 7), s(4, 10), s(7, 10)}, {s(5, 8), s(5, 10), s(8, 10)}, {s(6, 9), s(6, 10), s(9, 10)}],
   [{s(0, 5), s(0, 10), s(5, 10)}, {s(1, 6), s(1, 10), s(6, 10)}, {s(2, 7), s(2, 10), s(7, 10)}, {s(3, 8), s(3, 10), s(8, 10)}, {s(4, 9), s(4, 10), s(9, 10)}]]

def tri583_M : Finset (Sym2 (Fin 11)) := {s(0, 2), s(1, 3), s(4, 7), s(5, 8), s(6, 9)}

def tri583_group (t : Finset (Sym2 (Fin 11))) : Fin 5 :=
  if t ⊆ finite_vertex_set_edge_encoding ({0, 5, 8, 10} : Finset (Fin 11)) then 0
  else if t ⊆ finite_vertex_set_edge_encoding ({1, 6, 9, 10} : Finset (Fin 11)) then 1
  else if t ⊆ finite_vertex_set_edge_encoding ({4, 7, 9, 10} : Finset (Fin 11)) then 2
  else if t ⊆ finite_vertex_set_edge_encoding ({1, 3, 8, 10} : Finset (Fin 11)) then 3
  else 4

def tri583_omitIdx (e : Sym2 (Fin 11)) : Fin 3 :=
  if e ∉ (tri583_Cl.getD 0 []).toFinset.biUnion id then 0
  else if e ∉ (tri583_Cl.getD 1 []).toFinset.biUnion id then 1 else 2

def tri583_omit (e : Sym2 (Fin 11)) : Finset (Finset (Sym2 (Fin 11))) :=
  (tri583_Cl.getD (tri583_omitIdx e) []).toFinset

def tri583_other (R : Finset (Fin 11)) : Fin 11 :=
  ((List.finRange 11).filter (fun w => decide (w ∈ R ∧ w ≠ 10))).headD 10

def tri583_root (R : Finset (Fin 11)) : Fin 11 :=
  if (10 : Fin 11) ∉ R then 10 else if tri583_other R = 0 then 1 else 0

def tri583_rank (R : Finset (Fin 11)) (v : Fin 11) : ℕ :=
  if (10 : Fin 11) ∉ R then (if v = 10 then 0 else 1)
  else ((([[0, 0, 3, 1, 2, 2, 1, 2, 1, 1, 0], [0, 0, 1, 2, 2, 1, 3, 1, 1, 2, 0], [0, 2, 0, 2, 2, 1, 3, 1, 1, 2, 0], [0, 2, 1, 0, 2, 1, 3, 1, 1, 2, 0], [0, 2, 1, 2, 0, 1, 3, 1, 1, 2, 0], [0, 2, 1, 2, 2, 0, 3, 1, 1, 2, 0], [0, 2, 1, 2, 2, 1, 0, 1, 1, 2, 0], [0, 2, 1, 2, 4, 1, 3, 0, 1, 3, 0], [0, 3, 1, 4, 2, 1, 3, 1, 0, 2, 0], [0, 2, 1, 2, 2, 1, 3, 1, 1, 0, 0], [0, 2, 1, 2, 2, 1, 3, 1, 1, 2, 0]] : List (List ℕ)).getD (tri583_other R).val []).getD v.val 0)


set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_family_eq :
    (Finset.univ.filter (fun t : Finset (Fin 11) => tri583_G.IsNClique 3 t)).image
      finite_vertex_set_edge_encoding = tri583_Fexp := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_P_sub :
    tri583_P ⊆ tri583_Fexp := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_P_card :
    tri583_P.card = 5 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_P_len :
    tri583_Pl.length = 5 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_P_disj :
    ∀ i j : Fin 5, i ≠ j → ∀ a b : Fin 11, s(a, b) ∈ tri583_Pl.getD i ∅ → s(a, b) ∉ tri583_Pl.getD j ∅ := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_cod_lo :
    ∀ a b : Fin 11, tri583_G.Adj a b → 2 ≤ (tri583_Fexp.filter (fun t => s(a, b) ∈ t)).card := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_cod_hi :
    ∀ a b : Fin 11, tri583_G.Adj a b → (tri583_Fexp.filter (fun t => s(a, b) ∈ t)).card ≤ 8 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_M_sub :
    tri583_M ⊆ tri583_P.biUnion id := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_M_one :
    ∀ i : Fin 5, (tri583_M ∩ tri583_Pl.getD i ∅).card = 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_forced :
    ((tri583_Fexp.filter (fun t => (t ∩ tri583_P.biUnion id).card = 1)).biUnion id) ∩ tri583_P.biUnion id ⊆ tri583_M := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_o_sub :
    ∀ a b : Fin 11, tri583_G.Adj a b → tri583_omit s(a, b) ⊆ tri583_Fexp := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_o_card :
    ∀ a b : Fin 11, tri583_G.Adj a b → (tri583_omit s(a, b)).card = 5 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_o_avoid :
    ∀ a b : Fin 11, tri583_G.Adj a b → s(a, b) ∉ (tri583_omit s(a, b)).biUnion id := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_C_len :
    ∀ c : Fin 3, (tri583_Cl.getD c []).length = 5 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_C_disj :
    ∀ c : Fin 3, ∀ i j : Fin 5, i ≠ j → ∀ a b : Fin 11, s(a, b) ∈ (tri583_Cl.getD c []).getD i ∅ → s(a, b) ∉ (tri583_Cl.getD c []).getD j ∅ := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_F_len :
    tri583_Fl.length = 20 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_group :
    ∀ i j : Fin 20, i ≠ j → tri583_group (tri583_Fl.getD i ∅) = tri583_group (tri583_Fl.getD j ∅) → ∃ a b : Fin 11, s(a, b) ∈ tri583_Fl.getD i ∅ ∧ s(a, b) ∈ tri583_Fl.getD j ∅ := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_rank :
    ∀ R : Finset (Fin 11), R.card ≤ 2 →
    tri583_root R ∉ R ∧ ∀ v : Fin 11, v ∉ R → v ≠ tri583_root R →
      ∃ u : Fin 11, u ∉ R ∧ tri583_G.Adj v u ∧ tri583_rank R u < tri583_rank R v := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tri583_check_cycle :
    Function.Injective ![s(0, 10), s(7, 10), s(9, 10), s(1, 10), (s(8, 10) : Sym2 (Fin 11))] ∧
    (∀ i, ![s(0, 10), s(7, 10), s(9, 10), s(1, 10), (s(8, 10) : Sym2 (Fin 11))] i ∈
      tri583_P.biUnion id \ tri583_M) ∧
    (∀ i, ∃ t ∈ tri583_Fexp, ![s(0, 10), s(7, 10), s(9, 10), s(1, 10), (s(8, 10) : Sym2 (Fin 11))] i ∈ t ∧
      ![s(0, 10), s(7, 10), s(9, 10), s(1, 10), (s(8, 10) : Sym2 (Fin 11))] (i + 1) ∈ t ∧
      ¬ t ⊆ tri583_P.biUnion id) := by
  decide +kernel

theorem tri583_index {α : Type*} [DecidableEq α] (l : List α) (d : α) (x : α)
    (hx : x ∈ l.toFinset) : ∃ n, n < l.length ∧ l.getD n d = x := by
  rw [List.mem_toFinset, List.mem_iff_getElem] at hx
  obtain ⟨n, hn, rfl⟩ := hx
  exact ⟨n, hn, by rw [List.getD_eq_getElem _ _ hn]⟩

theorem tri583_disjoint_of_index (l : List (Finset (Sym2 (Fin 11)))) (hl : l.length = 5)
    (h : ∀ i j : Fin 5, i ≠ j → ∀ a b : Fin 11, s(a, b) ∈ l.getD i ∅ → s(a, b) ∉ l.getD j ∅)
    (x y : Finset (Sym2 (Fin 11))) (hx : x ∈ l.toFinset) (hy : y ∈ l.toFinset) (hxy : x ≠ y) :
    Disjoint x y := by
  obtain ⟨i, hi, rfl⟩ := tri583_index l ∅ x hx
  obtain ⟨j, hj, rfl⟩ := tri583_index l ∅ y hy
  rw [Finset.disjoint_left]
  intro e he
  induction e using Sym2.ind with
  | h a b =>
    have hij : (⟨i, hl ▸ hi⟩ : Fin 5) ≠ ⟨j, hl ▸ hj⟩ := by
      intro h'; apply hxy; simp only [Fin.mk.injEq] at h'; rw [h']
    exact h _ _ hij a b he

theorem tri583_conn_of_rank {V : Type*} (G : SimpleGraph V) (S : Set V) (r : V) (hr : r ∈ S)
    (rank : V → ℕ) (h : ∀ v ∈ S, v ≠ r → ∃ u ∈ S, G.Adj v u ∧ rank u < rank v) :
    (G.induce S).Connected := by
  have key : ∀ n, ∀ v (hv : v ∈ S), rank v ≤ n →
      (G.induce S).Reachable ⟨v, hv⟩ ⟨r, hr⟩ := by
    intro n
    induction n with
    | zero =>
      intro v hv hrk
      by_cases hvr : v = r
      · subst hvr; rfl
      · obtain ⟨u, _, _, hlt⟩ := h v hv hvr; omega
    | succ n ih =>
      intro v hv hrk
      by_cases hvr : v = r
      · subst hvr; rfl
      · obtain ⟨u, hu, hadj, hlt⟩ := h v hv hvr
        have hA : (G.induce S).Adj ⟨v, hv⟩ ⟨u, hu⟩ := by simpa using hadj
        exact hA.reachable.trans (ih u hu (by omega))
  have : Nonempty S := ⟨⟨r, hr⟩⟩
  exact SimpleGraph.Connected.mk (fun x y =>
    (key _ x.1 x.2 le_rfl).trans (key _ y.1 y.2 le_rfl).symm)

theorem simple_graph_stable_min_two_triangles_conflict_five_cycle :
    ∃ (G : SimpleGraph (Fin 11))
      (P : Finset (Finset (Sym2 (Fin 11)))) (M : Finset (Sym2 (Fin 11))),
      let F := simple_graph_triangle_edge_family G
      let U := P.biUnion id
      P ⊆ F ∧ P.card = 5 ∧
      (P : Set (Finset (Sym2 (Fin 11)))).Pairwise Disjoint ∧
      (∀ Q : Finset (Finset (Sym2 (Fin 11))),
        Q ⊆ F → (Q : Set (Finset (Sym2 (Fin 11)))).Pairwise Disjoint → Q.card ≤ 5) ∧
      (∀ e ∈ G.edgeSet, ∃ Q : Finset (Finset (Sym2 (Fin 11))),
        Q ⊆ F ∧ Q.card = 5 ∧
        (Q : Set (Finset (Sym2 (Fin 11)))).Pairwise Disjoint ∧ e ∉ Q.biUnion id) ∧
      (∀ e ∈ G.edgeSet, 2 ≤ (F.filter (fun t => e ∈ t)).card ∧
        (F.filter (fun t => e ∈ t)).card ≤ 8) ∧
      (∀ R : Finset (Fin 11), R.card ≤ 2 → (G.induce {v | v ∉ R}).Connected) ∧
      M ⊆ U ∧ (∀ p ∈ P, (M ∩ p).card = 1) ∧
      (((F.filter (fun t => (t ∩ U).card = 1)).biUnion id) ∩ U) ⊆ M ∧
      ∃ f : Fin 5 → Sym2 (Fin 11), Function.Injective f ∧
        (∀ i, f i ∈ U \ M) ∧
        (∀ i, ∃ t ∈ F, f i ∈ t ∧ f (i + 1) ∈ t ∧ ¬ t ⊆ U) := by
  have hF : simple_graph_triangle_edge_family tri583_G = tri583_Fexp := by
    unfold simple_graph_triangle_edge_family
    rw [Finset.filter_congr_decidable]
    exact tri583_check_family_eq
  refine ⟨tri583_G, tri583_P, tri583_M, ?_⟩
  rw [hF]
  intro F U
  refine ⟨tri583_check_P_sub, tri583_check_P_card, ?_, ?_, ?_, ?_, ?_, tri583_check_M_sub, ?_,
    tri583_check_forced, ⟨_, tri583_check_cycle⟩⟩
  · intro x hx y hy hxy
    exact tri583_disjoint_of_index tri583_Pl tri583_check_P_len tri583_check_P_disj x y hx hy hxy
  · intro Q hQ hdisj
    calc Q.card ≤ (Finset.univ : Finset (Fin 5)).card := by
          apply Finset.card_le_card_of_injOn tri583_group
          · intro _ _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
          · intro x hx y hy hxy
            by_contra hne
            have hd := hdisj hx hy hne
            obtain ⟨i, hi, rfl⟩ := tri583_index tri583_Fl ∅ x (hQ hx)
            obtain ⟨j, hj, rfl⟩ := tri583_index tri583_Fl ∅ y (hQ hy)
            rw [tri583_check_F_len] at hi hj
            have hij : (⟨i, hi⟩ : Fin 20) ≠ ⟨j, hj⟩ := by
              intro h'; apply hne; simp only [Fin.mk.injEq] at h'; rw [h']
            obtain ⟨a, b, h1, h2⟩ := tri583_check_group _ _ hij hxy
            exact Finset.disjoint_left.mp hd h1 h2
      _ = 5 := by simp
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      refine ⟨tri583_omit s(a, b), tri583_check_o_sub a b he, tri583_check_o_card a b he, ?_,
        tri583_check_o_avoid a b he⟩
      intro x hx y hy hxy
      exact tri583_disjoint_of_index _ (tri583_check_C_len _) (tri583_check_C_disj _) x y hx hy hxy
  · intro e he
    induction e using Sym2.ind with
    | h a b => exact ⟨tri583_check_cod_lo a b he, tri583_check_cod_hi a b he⟩
  · intro R hR
    obtain ⟨hroot, hstep⟩ := tri583_check_rank R hR
    exact tri583_conn_of_rank tri583_G {v | v ∉ R} (tri583_root R) hroot (tri583_rank R)
      (fun v hv hvr => by
        obtain ⟨u, hu, hadj, hlt⟩ := hstep v hv hvr
        exact ⟨u, hu, hadj, hlt⟩)
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := tri583_index tri583_Pl ∅ p hp
    rw [tri583_check_P_len] at hi
    exact tri583_check_M_one ⟨i, hi⟩
