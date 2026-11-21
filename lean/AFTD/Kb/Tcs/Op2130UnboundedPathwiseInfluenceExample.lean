import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolStep

/-!
# op_2130_unbounded_pathwise_influence_example

Topic: online_algorithms   Node: 2f54459e2f52

Provenance: helper lemma. OP-2130, exact recurrent influence cycle on a four-vertex path, experiments 37049 and 37051

A fixed nine-request prefix and ten-request path block have the following property: for any numbers of blocks before and after, changing only the first tie coin of one block changes the final discrepancy of vertex 2 from 0 to 2. Hence one tape can have arbitrarily many individually influential coins at a single vertex.
-/

private def op2130i_update (d : Fin 4 → ℤ) (p : Fin 3 × Bool) : Fin 4 → ℤ :=
  let a : Fin 4 := ⟨p.1.val, by omega⟩
  let b : Fin 4 := ⟨p.1.val + 1, by omega⟩
  let sign := if d a < d b then true else if d b < d a then false else p.2
  carpool_step 4 d (a,b) sign

private def op2130i_run (d : Fin 4 → ℤ) (w : List (Fin 3 × Bool)) : Fin 4 → ℤ :=
  w.foldl op2130i_update d

private def op2130i_start : List (Fin 3 × Bool) :=
  [(0,false),(1,false),(2,false),(1,true),(0,false),(2,true),(1,false),(1,false),(0,false)]
private def op2130i_block : List (Fin 3 × Bool) :=
  [(2,false),(0,false),(1,false),(0,false),(1,true),(0,false),(2,true),(1,false),(1,false),(0,false)]
private def op2130i_flipped : List (Fin 3 × Bool) :=
  [(2,true),(0,false),(1,false),(0,false),(1,true),(0,false),(2,true),(1,false),(1,false),(0,false)]
private def op2130i_x : Fin 4 → ℤ := ![-1,1,0,0]
private def op2130i_y : Fin 4 → ℤ := ![-1,1,2,-2]

private lemma op2130i_base : op2130i_run (fun _ => 0) op2130i_start = op2130i_x := by decide
private lemma op2130i_stable_x : op2130i_run op2130i_x op2130i_block = op2130i_x := by decide
private lemma op2130i_stable_y : op2130i_run op2130i_y op2130i_block = op2130i_y := by decide
private lemma op2130i_switch : op2130i_run op2130i_x op2130i_flipped = op2130i_y := by decide
private lemma op2130i_fixed_repeat (d : Fin 4 → ℤ) (h : op2130i_run d op2130i_block = d) :
    ∀ k, op2130i_run d (List.flatten (List.replicate k op2130i_block)) = d := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.flatten_cons, op2130i_run, List.foldl_append] at *
    rw [h]
    exact ih

private theorem op2130i_influence_cycle (k j : ℕ) :
    op2130i_run (fun _ => 0)
      (op2130i_start ++ (List.replicate k op2130i_block).flatten ++
        op2130i_flipped ++ (List.replicate j op2130i_block).flatten) 2 = 2 ∧
    op2130i_run (fun _ => 0)
      (op2130i_start ++ (List.replicate (k + 1 + j) op2130i_block).flatten) 2 = 0 := by
  have hx := op2130i_fixed_repeat op2130i_x op2130i_stable_x
  have hy := op2130i_fixed_repeat op2130i_y op2130i_stable_y
  have hbase := op2130i_base
  have hs := op2130i_switch
  simp only [op2130i_run] at hbase hs
  constructor
  · simp only [op2130i_run, List.foldl_append] at *
    rw [hbase, hx k, hs, hy j]
    rfl
  · simp only [op2130i_run, List.foldl_append] at *
    rw [hbase, hx (k + 1 + j)]
    rfl

theorem op_2130_unbounded_pathwise_influence_example (k j : ℕ) :
    let update := fun (d : Fin 4 → ℤ) (p : Fin 3 × Bool) =>
      let a : Fin 4 := ⟨p.1.val, by omega⟩
      let b : Fin 4 := ⟨p.1.val + 1, by omega⟩
      let sign := if d a < d b then true else if d b < d a then false else p.2
      carpool_step 4 d (a,b) sign
    let run := fun (d : Fin 4 → ℤ) (w : List (Fin 3 × Bool)) => w.foldl update d
    let start : List (Fin 3 × Bool) :=
      [(0,false),(1,false),(2,false),(1,true),(0,false),(2,true),(1,false),(1,false),(0,false)]
    let block : List (Fin 3 × Bool) :=
      [(2,false),(0,false),(1,false),(0,false),(1,true),(0,false),(2,true),(1,false),(1,false),(0,false)]
    let flipped : List (Fin 3 × Bool) :=
      [(2,true),(0,false),(1,false),(0,false),(1,true),(0,false),(2,true),(1,false),(1,false),(0,false)]
    run (fun _ => 0) (start ++ (List.replicate k block).flatten ++ flipped ++ (List.replicate j block).flatten) 2 = 2 ∧
    run (fun _ => 0) (start ++ (List.replicate (k + 1 + j) block).flatten) 2 = 0 := by
  exact op2130i_influence_cycle k j
