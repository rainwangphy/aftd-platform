import AFTD.Prelude
import AFTD.Kb.Tcs.TenVertexExchangeGraph
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamily
import AFTD.Kb.Tcs.TenVertexExchangeFamilyEq
import AFTD.Kb.Tcs.TenVertexExchangeEdgeSet
import AFTD.Kb.Tcs.TenVertexExchangeEdges
import AFTD.Kb.Tcs.TenVertexExchangeTriangle
import AFTD.Kb.Tcs.TenVertexExchangeFamily

/-!
# ten_vertex_exchange_triangle_connected

Topic: graphs   Node: 8d29ee730248

Provenance: helper lemma. Explicit ten-vertex witness for simple_graph_stable_point_irreducible_forced_exchange_barrier_counterexample.

After excluding each graph edge, the triangle family is connected under sharing any other edge.
-/

namespace tvaux

def td : Fin 52 → Fin 10 × Fin 10 × Fin 10 :=
  ![(0,1,2),(0,1,3),(0,1,7),(0,2,3),(0,2,7),(0,2,8),(0,2,9),(0,3,6),(0,3,7),(0,3,9),
    (0,6,7),(0,6,8),(0,6,9),(0,7,8),(0,8,9),(1,2,3),(1,2,4),(1,2,5),(1,2,7),(1,3,4),
    (1,3,5),(1,3,7),(1,4,5),(1,4,7),(2,3,4),(2,3,5),(2,3,7),(2,3,9),(2,4,5),(2,4,7),
    (2,4,8),(2,5,8),(2,5,9),(2,7,8),(2,8,9),(3,4,5),(3,4,6),(3,4,7),(3,5,6),(3,5,9),
    (3,6,7),(3,6,9),(4,5,6),(4,5,8),(4,6,7),(4,6,8),(4,7,8),(5,6,8),(5,6,9),(5,8,9),
    (6,7,8),(6,8,9)]

def ed : Fin 35 → Fin 10 × Fin 10 :=
  ![(0,1),(0,2),(0,3),(0,6),(0,7),(0,8),(0,9),(1,2),(1,3),(1,4),(1,5),(1,7),(2,3),
    (2,4),(2,5),(2,7),(2,8),(2,9),(3,4),(3,5),(3,6),(3,7),(3,9),(4,5),(4,6),(4,7),
    (4,8),(5,6),(5,8),(5,9),(6,7),(6,8),(6,9),(7,8),(8,9)]

def vs (i : Fin 52) : Finset (Fin 10) := let t := td i; {t.1, t.2.1, t.2.2}

def ep (k : Fin 35) : Finset (Fin 10) := let p := ed k; {p.1, p.2}

def tri (i : Fin 52) : Finset (Sym2 (Fin 10)) :=
  let t := td i; ten_vertex_exchange_triangle t.1 t.2.1 t.2.2

def eE (k : Fin 35) : Sym2 (Fin 10) := let p := ed k; s(p.1, p.2)

def shareB (k : Fin 35) (i j : Fin 52) : Bool :=
  let u := vs i ∩ vs j
  decide (2 ≤ u.card) && (decide (3 ≤ u.card) || decide (u ≠ ep k))

abbrev Sh (e : Sym2 (Fin 10)) (x y : Finset (Sym2 (Fin 10))) : Prop :=
  ∃ f ∈ x, f ∈ y ∧ f ≠ e

abbrev R (e : Sym2 (Fin 10)) (x y : Finset (Sym2 (Fin 10))) : Prop :=
  x ∈ ten_vertex_exchange_family ∧ y ∈ ten_vertex_exchange_family ∧ Sh e x y

def chk (k : Fin 35) (i j : Fin 52) : Bool :=
  !(shareB k i j) || decide (0 < ((tri j).filter (fun f => f ∈ tri i ∧ f ≠ eE k)).card)

set_option maxHeartbeats 4000000 in
theorem chk_all : ∀ (k : Fin 35) (i j : Fin 52), chk k i j = true := by decide

theorem bridge (k : Fin 35) (i j : Fin 52) (h : shareB k i j = true) :
    Sh (eE k) (tri i) (tri j) := by
  have hc : chk k i j = true := chk_all k i j
  rw [chk, h] at hc
  simp only [Bool.not_true, Bool.false_or] at hc
  have hp : 0 < ((tri j).filter (fun f => f ∈ tri i ∧ f ≠ eE k)).card := of_decide_eq_true hc
  obtain ⟨f, hf⟩ := Finset.card_pos.mp hp
  obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hf
  exact ⟨f, h2, h1, h3⟩

def step (k : Fin 35) (S : Finset (Fin 52)) : Finset (Fin 52) :=
  S ∪ ((Finset.univ : Finset (Fin 52)).filter
        (fun j => (S.filter (fun i => shareB k i j = true)).Nonempty))

def cl (k : Fin 35) : Nat → Finset (Fin 52)
  | 0 => {0}
  | n + 1 => step k (cl k n)

theorem step_mem (k : Fin 35) (S : Finset (Fin 52)) (j : Fin 52) :
    j ∈ step k S ↔ j ∈ S ∨ ∃ i ∈ S, shareB k i j = true := by
  simp [step, Finset.mem_filter, Finset.Nonempty]

set_option maxHeartbeats 4000000 in
theorem cl_full : ∀ k : Fin 35, cl k 5 = (Finset.univ : Finset (Fin 52)) := by decide

set_option maxHeartbeats 4000000 in
theorem family_eq : ten_vertex_exchange_family = (Finset.univ : Finset (Fin 52)).image tri := by
  decide

set_option maxHeartbeats 4000000 in
theorem edges_eq : ten_vertex_exchange_edges = (Finset.univ : Finset (Fin 35)).image eE := by
  decide

theorem tri_mem (i : Fin 52) : tri i ∈ ten_vertex_exchange_family := by
  rw [family_eq]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

theorem R_symm (e : Sym2 (Fin 10)) {x y : Finset (Sym2 (Fin 10))} (h : R e x y) : R e y x := by
  obtain ⟨hx, hy, f, hf, hf', hne⟩ := h
  exact ⟨hy, hx, f, hf', hf, hne⟩

theorem rtg_symm (r : Finset (Sym2 (Fin 10)) → Finset (Sym2 (Fin 10)) → Prop)
    (hs : ∀ x y, r x y → r y x) {x y : Finset (Sym2 (Fin 10))}
    (h : Relation.ReflTransGen r x y) : Relation.ReflTransGen r y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hs _ _ hbc) ih

theorem cl_mem (k : Fin 35) : ∀ (n : Nat) (i : Fin 52), i ∈ cl k n →
    Relation.ReflTransGen (R (eE k)) (tri 0) (tri i) := by
  intro n
  induction n with
  | zero =>
    intro i hi
    have h0 : i = 0 := by
      simpa [cl] using hi
    subst h0
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro i hi
    have hs : i ∈ step k (cl k n) := by simpa [cl] using hi
    rw [step_mem] at hs
    rcases hs with hs | ⟨i', hi', hsh⟩
    · exact ih i hs
    · exact (ih i' hi').tail ⟨tri_mem i', tri_mem i, bridge k i' i hsh⟩

end tvaux

theorem ten_vertex_exchange_triangle_connected : ∀ e ∈ ten_vertex_exchange_graph.edgeSet, ∀ a ∈ simple_graph_triangle_edge_family ten_vertex_exchange_graph, ∀ b ∈ simple_graph_triangle_edge_family ten_vertex_exchange_graph, Relation.ReflTransGen (fun x y : Finset (Sym2 (Fin 10)) => x ∈ simple_graph_triangle_edge_family ten_vertex_exchange_graph ∧ y ∈ simple_graph_triangle_edge_family ten_vertex_exchange_graph ∧ ∃ f ∈ x, f ∈ y ∧ f ≠ e) a b := by
  intro e he a ha b hb
  rw [ten_vertex_exchange_family_eq] at ha hb
  have he' : e ∈ ten_vertex_exchange_edges := by
    have h2 : e ∈ (ten_vertex_exchange_edges : Set (Sym2 (Fin 10))) := by
      rw [ten_vertex_exchange_edge_set.1]; exact he
    simpa using h2
  rw [tvaux.edges_eq] at he'
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp he'
  rw [tvaux.family_eq] at ha hb
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ha
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hb
  have hi' : i ∈ tvaux.cl k 5 := by
    rw [tvaux.cl_full]; exact Finset.mem_univ i
  have hj' : j ∈ tvaux.cl k 5 := by
    rw [tvaux.cl_full]; exact Finset.mem_univ j
  have h1 := tvaux.cl_mem k 5 i hi'
  have h2 := tvaux.cl_mem k 5 j hj'
  have h3 : Relation.ReflTransGen (tvaux.R (tvaux.eE k)) (tvaux.tri i) (tvaux.tri j) :=
    (tvaux.rtg_symm _ (fun x y => tvaux.R_symm _) h1).trans h2
  have key : Relation.ReflTransGen (tvaux.R e) (tvaux.tri i) (tvaux.tri j) := by
    rw [← hk]
    exact h3
  rw [← hi, ← hj, ten_vertex_exchange_family_eq]
  exact key
