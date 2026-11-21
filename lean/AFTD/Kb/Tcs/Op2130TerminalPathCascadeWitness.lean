import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130BoundedPathHasNonincreasingEdge
import AFTD.Kb.Tcs.Op2130CenteredPathPotentialBound
import AFTD.Kb.Tcs.Op2130CenteredPathPotentialRightStep
import AFTD.Kb.Tcs.Op2130RightMovesAreGreedy
import AFTD.Kb.Tcs.CarpoolStep
import AFTD.Kb.Tcs.CarpoolGreedyOrientations
import AFTD.Kb.Tcs.MaxVertexDiscrepancy

/-!
# op_2130_terminal_path_cascade_witness

Topic: online_algorithms   Node: 8c1d9cad4645

Provenance: helper lemma. OP-2130: the same first-hit construction as op_2130_path_cascade_witness, retaining the terminal discrepancy for the independent-block argument

For every positive D, there is a fixed sequence of at most D³ requests on the 2D-vertex path and a fixed coin tape for which the terminal discrepancy is at least D.
-/

open Function

private noncomputable def op2130_terminal_path_choice (D : ℕ) (hD : 1 ≤ D) (d : Fin (2 * D) → ℤ) : Fin (2 * D - 1) :=
  if h : ∃ i : Fin (2 * D - 1), d ⟨i.val, by omega⟩ ≥ d ⟨i.val + 1, by omega⟩
  then Classical.choose h else ⟨0, by omega⟩

private noncomputable def op2130_terminal_path_step (D : ℕ) (hD : 1 ≤ D) (d : Fin (2 * D) → ℤ) : Fin (2 * D) → ℤ :=
  let i := op2130_terminal_path_choice D hD d
  carpool_step (2 * D) d (⟨i.val, by omega⟩, ⟨i.val + 1, by omega⟩) false

private def op2130_terminal_path_energy (D : ℕ) (d : Fin (2 * D) → ℤ) : ℤ :=
  ∑ i, (2 * (i.val : ℤ) + 1 - 2 * (D : ℤ)) * d i

private def op2130_terminal_path_hit (D : ℕ) (d : Fin (2 * D) → ℤ) : Prop :=
  ∃ i, (D : ℤ) ≤ |d i|

private lemma op2130_terminal_path_choice_legal (D : ℕ) (hD : 1 ≤ D) (d : Fin (2 * D) → ℤ)
    (h : ∃ i : Fin (2 * D - 1), d ⟨i.val, by omega⟩ ≥ d ⟨i.val + 1, by omega⟩) :
    let i := op2130_terminal_path_choice D hD d
    d ⟨i.val, by omega⟩ ≥ d ⟨i.val + 1, by omega⟩ := by
  classical
  simp only [op2130_terminal_path_choice, dif_pos h]
  exact Classical.choose_spec h

private lemma op2130_terminal_finite_walk_hits (α : Type) (G : α → Prop) (f : α → α)
    (V : α → ℤ) (s : α) (B : ℕ)
    (hzero : V s = 0)
    (hstep : ∀ x, ¬ G x → V (f x) = V x + 2)
    (hbound : ∀ x, ¬ G x → V x ≤ 2 * (B : ℤ)) :
    ∃ k ≤ B + 1, G ((f^[k]) s) := by
  classical
  by_contra h
  push_neg at h
  have hv : ∀ k : ℕ, k ≤ B + 1 → V ((f^[k]) s) = 2 * (k : ℤ) := by
    intro k hk
    induction k with
    | zero => simpa using hzero
    | succ k ih =>
      have hk' : k ≤ B + 1 := by omega
      have hn : ¬ G ((f^[k]) s) := h k hk'
      rw [Function.iterate_succ_apply']
      rw [hstep _ hn, ih hk']
      push_cast
      ring
  have hlast := h (B + 1) (by omega)
  have hb := hbound ((f^[B + 1]) s) hlast
  have he := hv (B + 1) (by omega)
  push_cast at he
  omega

private theorem op2130_terminal_path_first_hit (D : ℕ) (hD : 1 ≤ D)
    (hbound : ∀ d : Fin (2 * D) → ℤ, (∀ i, |d i| < (D : ℤ)) →
      op2130_terminal_path_energy D d ≤ 2 * (D : ℤ)^2 * ((D : ℤ) - 1))
    (hstep : ∀ d : Fin (2 * D) → ℤ, op2130_terminal_path_energy D (op2130_terminal_path_step D hD d) = op2130_terminal_path_energy D d + 2) :
    ∃ k ≤ D * D * (D - 1) + 1,
      op2130_terminal_path_hit D (((op2130_terminal_path_step D hD)^[k]) (fun _ => 0)) ∧
      ∀ j < k, ¬ op2130_terminal_path_hit D (((op2130_terminal_path_step D hD)^[j]) (fun _ => 0)) := by
  classical
  let f := op2130_terminal_path_step D hD
  let z : Fin (2 * D) → ℤ := fun _ => 0
  let B := D * D * (D - 1)
  have h0 : op2130_terminal_path_energy D z = 0 := by simp [op2130_terminal_path_energy, z]
  have hprog : ∀ d, ¬ op2130_terminal_path_hit D d → op2130_terminal_path_energy D (f d) = op2130_terminal_path_energy D d + 2 := by
    intro d _
    exact hstep d
  have hb : ∀ d, ¬ op2130_terminal_path_hit D d → op2130_terminal_path_energy D d ≤ 2 * (B : ℤ) := by
    intro d hn
    have hlo : ∀ i, |d i| < (D : ℤ) := by
      intro i
      exact lt_of_not_ge (fun hi => hn ⟨i, hi⟩)
    have hf := hbound d hlo
    have hc : ((D - 1 : ℕ) : ℤ) = (D : ℤ) - 1 := by omega
    dsimp [B]
    push_cast
    rw [hc]
    nlinarith
  obtain ⟨m, hm, hmhit⟩ := op2130_terminal_finite_walk_hits _ (op2130_terminal_path_hit D) f (op2130_terminal_path_energy D) z B h0 hprog hb
  have ex : ∃ k, op2130_terminal_path_hit D ((f^[k]) z) := ⟨m, hmhit⟩
  refine ⟨Nat.find ex, ?_, Nat.find_spec ex, ?_⟩
  · exact le_trans (Nat.find_min' ex hmhit) hm
  · intro j hj
    exact Nat.find_min ex hj

private noncomputable def op2130_terminal_path_edge (D : ℕ) (hD : 1 ≤ D) (t : ℕ) : Fin (2 * D) × Fin (2 * D) :=
  let i := op2130_terminal_path_choice D hD (((op2130_terminal_path_step D hD)^[t]) (fun _ => 0))
  (⟨i.val, by omega⟩, ⟨i.val + 1, by omega⟩)

private noncomputable def op2130_terminal_path_edges (D : ℕ) (hD : 1 ≤ D) (k : ℕ) : List (Fin (2 * D) × Fin (2 * D)) :=
  (List.range k).map (op2130_terminal_path_edge D hD)

private lemma op2130_terminal_path_edges_length (D : ℕ) (hD : 1 ≤ D) (k : ℕ) : (op2130_terminal_path_edges D hD k).length = k := by
  simp [op2130_terminal_path_edges]

private lemma op2130_terminal_path_edges_fold (D : ℕ) (hD : 1 ≤ D) (k : ℕ) :
    (op2130_terminal_path_edges D hD k).foldl (fun d e => carpool_step (2 * D) d e false) (fun _ => 0) =
      ((op2130_terminal_path_step D hD)^[k]) (fun _ => 0) := by
  induction k with
  | zero => simp [op2130_terminal_path_edges]
  | succ k ih =>
      change ((List.range (k + 1)).map (op2130_terminal_path_edge D hD)).foldl _ _ = _
      rw [List.range_succ, List.map_append, List.foldl_append]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      change carpool_step _ ((op2130_terminal_path_edges D hD k).foldl _ _) (op2130_terminal_path_edge D hD k) false = _
      rw [ih, Function.iterate_succ_apply']
      rfl

private lemma op2130_terminal_path_edges_take (D : ℕ) (hD : 1 ≤ D) (j k : ℕ) (hjk : j ≤ k) :
    (op2130_terminal_path_edges D hD k).take j = op2130_terminal_path_edges D hD j := by
  simp [op2130_terminal_path_edges, ← List.map_take, List.take_range, Nat.min_eq_left hjk]

private lemma op2130_terminal_path_edges_index (D : ℕ) (hD : 1 ≤ D) (j k : ℕ) (hjk : j < k) :
    (op2130_terminal_path_edges D hD k)[j]'(by simp [op2130_terminal_path_edges]; omega) = op2130_terminal_path_edge D hD j := by
  simp [op2130_terminal_path_edges, hjk]

private lemma op2130_terminal_path_edges_valid (D : ℕ) (hD : 1 ≤ D) (k : ℕ) :
    ∀ e ∈ op2130_terminal_path_edges D hD k, (SimpleGraph.pathGraph (2 * D)).Adj e.1 e.2 := by
  intro e he
  simp only [op2130_terminal_path_edges, List.mem_map, List.mem_range] at he
  obtain ⟨t, ht, rfl⟩ := he
  simp [op2130_terminal_path_edge, SimpleGraph.pathGraph_adj]

private lemma op2130_terminal_path_edges_greedy_legal (D : ℕ) (hD : 1 ≤ D) (k : ℕ)
    (hdesc : ∀ d : Fin (2 * D) → ℤ, (∀ i, |d i| < (D : ℤ)) →
      ∃ i : Fin (2 * D - 1), d ⟨i.val, by omega⟩ ≥ d ⟨i.val + 1, by omega⟩)
    (hbefore : ∀ j < k, ¬ op2130_terminal_path_hit D (((op2130_terminal_path_step D hD)^[j]) (fun _ => 0))) :
    ∀ j (hj : j < (op2130_terminal_path_edges D hD k).length),
      let d := ((op2130_terminal_path_edges D hD k).take j).foldl (fun d e => carpool_step (2 * D) d e false) (fun _ => 0)
      d ((op2130_terminal_path_edges D hD k)[j]).2 ≤ d ((op2130_terminal_path_edges D hD k)[j]).1 := by
  intro j hj
  have hjk : j < k := by simpa [op2130_terminal_path_edges_length] using hj
  rw [op2130_terminal_path_edges_take D hD j k (by omega), op2130_terminal_path_edges_fold, op2130_terminal_path_edges_index D hD j k hjk]
  let d := ((op2130_terminal_path_step D hD)^[j]) (fun _ => 0)
  have hlo : ∀ i, |d i| < (D : ℤ) := by
    intro i
    exact lt_of_not_ge (fun hi => hbefore j hjk ⟨i, hi⟩)
  have hh := op2130_terminal_path_choice_legal D hD d (hdesc d hlo)
  exact hh

private theorem op2130_terminal_witness_from_local_facts (D : ℕ) (hD : 1 ≤ D)
    (hdesc : ∀ d : Fin (2 * D) → ℤ, (∀ i, |d i| < (D : ℤ)) →
      ∃ i : Fin (2 * D - 1), d ⟨i.val, by omega⟩ ≥ d ⟨i.val + 1, by omega⟩)
    (hbound : ∀ d : Fin (2 * D) → ℤ, (∀ i, |d i| < (D : ℤ)) →
      op2130_terminal_path_energy D d ≤ 2 * (D : ℤ)^2 * ((D : ℤ) - 1))
    (hstep : ∀ d : Fin (2 * D) → ℤ, op2130_terminal_path_energy D (op2130_terminal_path_step D hD d) = op2130_terminal_path_energy D d + 2)
    (hgreedy : ∀ (edges : List (Fin (2 * D) × Fin (2 * D))),
      (∀ j (hj : j < edges.length), let d := (edges.take j).foldl (fun d e => carpool_step (2 * D) d e false) (fun _ => 0);
        d (edges[j]).2 ≤ d (edges[j]).1) →
      carpool_greedy_orientations (2 * D) edges (List.replicate edges.length false) = List.replicate edges.length false)
    :
    ∃ (edges : List (Fin (2 * D) × Fin (2 * D))),
      (∀ e ∈ edges, (SimpleGraph.pathGraph (2 * D)).Adj e.1 e.2) ∧
      edges.length ≤ D ^ 3 ∧
      ∃ coin : Fin edges.length → Bool,
        D ≤ max_vertex_discrepancy (2 * D) ((edges.zip (carpool_greedy_orientations (2 * D) edges (List.ofFn coin))).foldl (fun d (e,b) => carpool_step (2 * D) d e b) (fun _ => 0)) := by
  classical
  obtain ⟨k, hk, hhit, hbefore⟩ := op2130_terminal_path_first_hit D hD hbound hstep
  let edges := op2130_terminal_path_edges D hD k
  have hlen : edges.length = k := op2130_terminal_path_edges_length D hD k
  have hvalid := op2130_terminal_path_edges_valid D hD k
  have hleg := op2130_terminal_path_edges_greedy_legal D hD k hdesc hbefore
  have hg := hgreedy edges hleg
  have hcubic : D * D * (D - 1) + 1 ≤ D ^ 3 := by
    calc
      _ ≤ D * D * (D - 1) + D * D := by nlinarith
      _ = D * D * ((D - 1) + 1) := by ring
      _ = D ^ 3 := by rw [Nat.sub_add_cancel hD]; ring
  refine ⟨edges, hvalid, ?_, fun _ => false, ?_⟩
  · rw [hlen]; exact le_trans hk hcubic
  · rw [List.ofFn_const, hg]
    have hz : ∀ (es : List (Fin (2 * D) × Fin (2 * D))) (d : Fin (2 * D) → ℤ),
        (es.zip (List.replicate es.length false)).foldl
          (fun d (e,b) => carpool_step (2 * D) d e b) d =
        es.foldl (fun d e => carpool_step (2 * D) d e false) d := by
      intro es
      induction es with
      | nil => intro d; rfl
      | cons e es ih =>
        intro d
        simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.foldl_cons]
        exact ih (carpool_step (2 * D) d e false)
    have hf : (edges.zip (List.replicate edges.length false)).foldl
        (fun (d : Fin (2 * D) → ℤ) (eb : (Fin (2 * D) × Fin (2 * D)) × Bool) => carpool_step (2 * D) d eb.1 eb.2)
          (fun _ : Fin (2 * D) => (0 : ℤ)) =
          ((op2130_terminal_path_step D hD)^[k]) (fun _ : Fin (2 * D) => (0 : ℤ)) := by
      rw [hz edges (fun _ => 0)]
      exact op2130_terminal_path_edges_fold D hD k
    obtain ⟨i, hi⟩ := hhit
    have hv : D ≤ max_vertex_discrepancy (2 * D) (((op2130_terminal_path_step D hD)^[k]) (fun _ => 0)) := by
      have hi' : D ≤ ((((op2130_terminal_path_step D hD)^[k]) (fun _ => 0)) i).natAbs := by
        rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
        exact hi
      unfold max_vertex_discrepancy
      exact le_trans hi' (Finset.le_sup (f := fun v : Fin (2 * D) => (((op2130_terminal_path_step D hD)^[k]) (fun _ => 0) v).natAbs) (Finset.mem_univ i))
    rw [hf]
    exact hv

theorem op_2130_terminal_path_cascade_witness : ∀ (D : ℕ), 1 ≤ D → ∃ (edges : List (Fin (2 * D) × Fin (2 * D))), (∀ e ∈ edges, (SimpleGraph.pathGraph (2 * D)).Adj e.1 e.2) ∧ edges.length ≤ D ^ 3 ∧ ∃ coin : Fin edges.length → Bool, D ≤ max_vertex_discrepancy (2 * D) ((edges.zip (carpool_greedy_orientations (2 * D) edges (List.ofFn coin))).foldl (fun d (e,b) => carpool_step (2 * D) d e b) (fun _ => 0)) := by
  intro D hD
  apply op2130_terminal_witness_from_local_facts D hD
  · intro d hd
    exact op_2130_bounded_path_has_nonincreasing_edge D hD d hd
  · intro d hd
    exact op_2130_centered_path_potential_bound D hD d hd
  · intro d
    unfold op2130_terminal_path_energy op2130_terminal_path_step
    exact op_2130_centered_path_potential_right_step D hD d (op2130_terminal_path_choice D hD d)
  · intro edges h
    exact op_2130_right_moves_are_greedy (2 * D) edges h
