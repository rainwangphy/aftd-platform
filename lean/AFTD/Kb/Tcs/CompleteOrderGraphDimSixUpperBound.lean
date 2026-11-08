import AFTD.Prelude
import AFTD.Kb.Tcs.OrderMoveToFront
import AFTD.Kb.Tcs.OrderGraph
import AFTD.Kb.Tcs.Order
import AFTD.Kb.Tcs.OrderGraphServes
import AFTD.Kb.Tcs.OrderGraphIsComplete
import AFTD.Kb.Tcs.V

/-!
# complete_order_graph_dim_six_upper_bound

Topic: combinatorics   Node: cb50d4e2cf8b

Provenance: helper lemma. arXiv:2610.39311 Corollary 8 -- Tight Asymptotic Bounds on the Size of Order Graphs

There exists a complete order graph of dimension 6 with exactly 40 edges.
-/

set_option maxHeartbeats 4000000

def complete_order_graph_dim_six_upper_bound_listToOrder (l : List (Fin 6)) : Order 6 :=
  if h : l.Nodup ∧ l.length = 6 then ⟨l, h.1, h.2⟩
  else ⟨[0, 1, 2, 3, 4, 5], by decide, by decide⟩

def complete_order_graph_dim_six_upper_bound_rawOrders : List (List (Fin 6)) := [
  [5, 1, 0, 4, 2, 3], [4, 3, 2, 1, 0, 5], [3, 2, 1, 0, 4, 5], [4, 5, 1, 2, 0, 3],
  [5, 1, 2, 4, 0, 3], [1, 2, 4, 0, 5, 3], [2, 4, 0, 5, 1, 3], [3, 4, 0, 5, 2, 1],
  [4, 0, 5, 2, 1, 3], [0, 5, 2, 1, 4, 3], [0, 1, 3, 5, 2, 4], [5, 2, 4, 1, 3, 0],
  [2, 4, 1, 3, 5, 0], [4, 1, 3, 5, 2, 0], [1, 3, 5, 2, 0, 4], [1, 4, 3, 0, 2, 5],
  [4, 3, 0, 2, 5, 1], [3, 0, 2, 4, 5, 1], [2, 3, 1, 5, 0, 4], [3, 1, 5, 0, 2, 4],
  [1, 5, 0, 2, 4, 3], [3, 5, 0, 2, 4, 1], [5, 0, 2, 4, 3, 1], [0, 2, 4, 3, 5, 1],
  [2, 4, 3, 5, 1, 0], [4, 3, 5, 2, 1, 0], [3, 5, 2, 1, 0, 4], [5, 2, 1, 0, 4, 3],
  [2, 1, 0, 4, 5, 3], [1, 0, 4, 5, 2, 3], [0, 4, 5, 2, 3, 1], [4, 5, 2, 3, 0, 1],
  [5, 2, 3, 0, 1, 4], [2, 3, 0, 1, 4, 5], [3, 0, 1, 4, 5, 2], [5, 3, 0, 1, 4, 2],
  [4, 5, 3, 0, 1, 2], [1, 4, 5, 3, 0, 2], [0, 1, 4, 5, 3, 2], [2, 0, 1, 4, 5, 3]
]

def complete_order_graph_dim_six_upper_bound_theOrders : List (Order 6) :=
  complete_order_graph_dim_six_upper_bound_rawOrders.map complete_order_graph_dim_six_upper_bound_listToOrder

def complete_order_graph_dim_six_upper_bound_findParent (pi : Order 6) (orders : List (Order 6)) : Option (Order 6 × Fin 6) :=
  match pi.elems with
  | [] => none
  | a :: _ =>
    (orders.filter (fun nu => nu ≠ pi && order_move_to_front a nu == pi)).head? |>.map (fun nu => (nu, a))

def complete_order_graph_dim_six_upper_bound_theEdges : List (Order 6 × Fin 6) :=
  complete_order_graph_dim_six_upper_bound_theOrders.filterMap
    (fun pi => complete_order_graph_dim_six_upper_bound_findParent pi complete_order_graph_dim_six_upper_bound_theOrders)

def complete_order_graph_dim_six_upper_bound_stepPaths
    (edges : List (Order 6 × Fin 6)) (paths : List (List (Order 6 × Fin 6))) : List (List (Order 6 × Fin 6)) :=
  paths.flatMap (fun p =>
    match p.getLast? with
    | none => []
    | some last =>
      let target := order_move_to_front last.2 last.1
      let labels := p.map Prod.snd
      (edges.filter (fun e => e.1 == target && !labels.contains e.2)).map (fun e => p ++ [e]))

def complete_order_graph_dim_six_upper_bound_allCandidatePaths : List (List (Order 6 × Fin 6)) :=
  let p1 := complete_order_graph_dim_six_upper_bound_theEdges.map (fun e => [e])
  let p2 := complete_order_graph_dim_six_upper_bound_stepPaths complete_order_graph_dim_six_upper_bound_theEdges p1
  let p3 := complete_order_graph_dim_six_upper_bound_stepPaths complete_order_graph_dim_six_upper_bound_theEdges p2
  let p4 := complete_order_graph_dim_six_upper_bound_stepPaths complete_order_graph_dim_six_upper_bound_theEdges p3
  let p5 := complete_order_graph_dim_six_upper_bound_stepPaths complete_order_graph_dim_six_upper_bound_theEdges p4
  let p6 := complete_order_graph_dim_six_upper_bound_stepPaths complete_order_graph_dim_six_upper_bound_theEdges p5
  p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6

def complete_order_graph_dim_six_upper_bound_G : OrderGraph 6 where
  V := complete_order_graph_dim_six_upper_bound_theOrders.toFinset
  E := complete_order_graph_dim_six_upper_bound_theEdges.toFinset
  edge_src := by decide
  edge_tgt := by decide

def complete_order_graph_dim_six_upper_bound_path_good
    (G : OrderGraph 6) (S : Finset (Fin 6)) (x : Fin 6) (p : List (Order 6 × Fin 6)) : Prop :=
  (∀ e ∈ p, e ∈ G.E) ∧
  p.IsChain (fun e1 e2 => e2.1 = order_move_to_front e1.2 e1.1) ∧
  p.length = S.card + 1 ∧
  (p.map Prod.snd).toFinset = insert x S ∧
  ((∃ e, p.head? = some e ∧ e.2 = x) ∨ (∃ e, p.getLast? = some e ∧ e.2 = x))

instance (G : OrderGraph 6) (S : Finset (Fin 6)) (x : Fin 6) (p : List (Order 6 × Fin 6)) :
    Decidable (complete_order_graph_dim_six_upper_bound_path_good G S x p) := by
  dsimp [complete_order_graph_dim_six_upper_bound_path_good]
  infer_instance

instance (G : OrderGraph 6) (candidates : List (List (Order 6 × Fin 6)))
    (S : Finset (Fin 6)) (x : Fin 6) :
    Decidable (∃ p ∈ candidates, complete_order_graph_dim_six_upper_bound_path_good G S x p) := by
  have : DecidablePred (complete_order_graph_dim_six_upper_bound_path_good G S x) := inferInstance
  infer_instance

lemma complete_order_graph_dim_six_upper_bound_serves_of_path_good
    {G : OrderGraph 6} {S : Finset (Fin 6)} {x : Fin 6} {p : List (Order 6 × Fin 6)}
    (h : complete_order_graph_dim_six_upper_bound_path_good G S x p) : order_graph_serves G S x := by
  rcases h with ⟨he, hchain, hlen, hset, hend⟩
  have hp_ne : p ≠ [] := by
    rintro rfl
    simp [List.head?, List.getLast?] at hend
  refine ⟨p, hp_ne, he, hchain, hlen, hset, ?_⟩
  rcases hend with (⟨e, heq, he2⟩ | ⟨e, heq, he2⟩)
  · left
    rw [List.head?_eq_some_head hp_ne, Option.some_inj] at heq
    rw [← he2, ← heq]
  · right
    rw [List.getLast?_eq_some_getLast hp_ne, Option.some_inj] at heq
    rw [← he2, ← heq]

theorem complete_order_graph_dim_six_upper_bound_check :
    ∀ (S : Finset (Fin 6)) (x : Fin 6), x ∉ S →
      ∃ p ∈ complete_order_graph_dim_six_upper_bound_allCandidatePaths,
        complete_order_graph_dim_six_upper_bound_path_good complete_order_graph_dim_six_upper_bound_G S x p := by
  decide

/-- Upper bound showing existence of a 40-edge complete order graph of dimension 6. -/
theorem complete_order_graph_dim_six_upper_bound :
    ∃ G : OrderGraph 6, order_graph_is_complete G ∧ G.E.card = 40 := by
  refine ⟨complete_order_graph_dim_six_upper_bound_G, ?_, by decide⟩
  intro S x hx
  have h := complete_order_graph_dim_six_upper_bound_check S x hx
  rcases h with ⟨p, -, hp⟩
  exact complete_order_graph_dim_six_upper_bound_serves_of_path_good hp
