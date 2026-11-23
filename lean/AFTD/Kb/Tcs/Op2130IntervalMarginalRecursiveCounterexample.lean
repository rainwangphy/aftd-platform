import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolStep

/-!
# op2130_interval_marginal_recursive_counterexample

Topic: online_algorithms   Node: 061c2a0a6d02

Provenance: helper lemma. OP-2130, counterexample to interval marginal log-concavity

For an explicit 33-request six-vertex path schedule, the recursively enumerated fair-coin greedy process in the list-state representation has interval {0,1} counts 2904555520, 2780823552, 2904555520 at discrepancies -2, 0, 2 respectively, so its interval marginal is not log-concave.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/- Weighted forward evaluation merges equal configurations after every request.
   This keeps the number of states small instead of enumerating 2^57 tapes. -/
def op2130_mc_step (d : List ℤ) (e : ℕ) (coin : Bool) : List ℤ :=
  let x := d.getD e 0
  let y := d.getD (e + 1) 0
  let a : ℤ := if x < y then 1 else if y < x then -1 else if coin then 1 else -1
  (d.set e (x + a)).set (e + 1) (y - a)

def op2130_mc_insert (s : List ℤ) (v : ℕ) : List (List ℤ × ℕ) → List (List ℤ × ℕ)
  | [] => [(s,v)]
  | (a,b)::xs => if a = s then (a,b+v)::xs else (a,b)::op2130_mc_insert s v xs

def op2130_mc_next (dist : List (List ℤ × ℕ)) (e : ℕ) : List (List ℤ × ℕ) :=
  dist.foldl (fun acc (s, v) =>
    op2130_mc_insert (op2130_mc_step s e true) v
      (op2130_mc_insert (op2130_mc_step s e false) v acc)) []

def op2130_mc_example_edges : List ℕ :=
  [2,3,1,0,4, 2,3,1,0,4, 2,3,1,0,4, 2,3,1,0,4, 2,3,1,0,4, 2,3,1,0,2,1,0,1]

def op2130_mc_eval (dist : List (List ℤ × ℕ)) (f : List ℤ → ℕ) : ℕ :=
  (dist.map fun (s, v) => v * f s).sum

theorem op2130_mc_eval_insert (s : List ℤ) (v : ℕ)
    (dist : List (List ℤ × ℕ)) (f : List ℤ → ℕ) :
    op2130_mc_eval (op2130_mc_insert s v dist) f =
      op2130_mc_eval dist f + v * f s := by
  induction dist with
  | nil => simp [op2130_mc_insert, op2130_mc_eval]
  | cons p ps ih =>
      rcases p with ⟨a,b⟩
      by_cases h : a = s
      · subst a
        simp [op2130_mc_insert, op2130_mc_eval, Nat.add_mul]
        omega
      · simp [op2130_mc_insert, op2130_mc_eval, h] at *
        omega

theorem op2130_mc_eval_fold (dist acc : List (List ℤ × ℕ))
    (e : ℕ) (f : List ℤ → ℕ) :
    op2130_mc_eval
      (dist.foldl (fun acc (s,v) =>
        op2130_mc_insert (op2130_mc_step s e true) v
          (op2130_mc_insert (op2130_mc_step s e false) v acc)) acc) f =
    op2130_mc_eval acc f +
      op2130_mc_eval dist (fun s => f (op2130_mc_step s e false) + f (op2130_mc_step s e true)) := by
  induction dist generalizing acc with
  | nil => simp [op2130_mc_eval]
  | cons p ps ih =>
      rcases p with ⟨s,v⟩
      simp only [List.foldl_cons, ih, op2130_mc_eval_insert]
      simp [op2130_mc_eval, Nat.mul_add]
      omega

theorem op2130_mc_eval_next (dist : List (List ℤ × ℕ))
    (e : ℕ) (f : List ℤ → ℕ) :
    op2130_mc_eval (op2130_mc_next dist e) f =
      op2130_mc_eval dist (fun s => f (op2130_mc_step s e false) + f (op2130_mc_step s e true)) := by
  simpa [op2130_mc_next, op2130_mc_eval] using op2130_mc_eval_fold dist [] e f

def op2130_mc_back (edges : List ℕ) (f : List ℤ → ℕ) : List ℤ → ℕ :=
  match edges with
  | [] => f
  | e::es => fun s =>
      op2130_mc_back es f (op2130_mc_step s e false) +
      op2130_mc_back es f (op2130_mc_step s e true)

theorem op2130_mc_forward_backward (edges : List ℕ) (dist : List (List ℤ × ℕ))
    (f : List ℤ → ℕ) :
    op2130_mc_eval (edges.foldl op2130_mc_next dist) f =
      op2130_mc_eval dist (op2130_mc_back edges f) := by
  induction edges generalizing dist with
  | nil => rfl
  | cons e es ih =>
      simp only [List.foldl_cons, ih, op2130_mc_eval_next, op2130_mc_back]


theorem op2130_mc_count_back_generic (edges : List ℕ) (z : ℤ) :
    op2130_mc_eval (edges.foldl op2130_mc_next [([0,0,0,0,0,0],1)])
      (fun d => if d.getD 0 0 + d.getD 1 0 = z then 1 else 0) =
    op2130_mc_back edges (fun d => if d.getD 0 0 + d.getD 1 0 = z then 1 else 0)
      [0,0,0,0,0,0] := by
  rw [op2130_mc_forward_backward]
  change 1 * op2130_mc_back edges
    (fun d => if d.getD 0 0 + d.getD 1 0 = z then 1 else 0) [0,0,0,0,0,0] + 0 = _
  simp only [Nat.one_mul, Nat.add_zero]

def op2130_mc_count (z : ℤ) : ℕ :=
  op2130_mc_eval (op2130_mc_example_edges.foldl op2130_mc_next [([0,0,0,0,0,0],1)])
    (fun d => if d.getD 0 0 + d.getD 1 0 = z then 1 else 0)

theorem op2130_interval_marginal_compressed_counterexample :
    op2130_mc_count (-2) = 2904555520 ∧ op2130_mc_count 0 = 2780823552 ∧
      op2130_mc_count 2 = 2904555520 := by
  decide

theorem op2130_mc_count_back (z : ℤ) :
    op2130_mc_count z = op2130_mc_back op2130_mc_example_edges
      (fun d => if d.getD 0 0 + d.getD 1 0 = z then 1 else 0) [0,0,0,0,0,0] :=
  op2130_mc_count_back_generic op2130_mc_example_edges z


theorem op2130_mc_step_agrees (a b c d e f : ℤ) (i : Fin 5) (coin : Bool) (v : Fin 6) :
    let s : List ℤ := [a,b,c,d,e,f]
    let x : Fin 6 := ⟨i.val, by omega⟩
    let y : Fin 6 := ⟨i.val + 1, by omega⟩
    let d0 : Fin 6 → ℤ := fun k => s.getD k.val 0
    (op2130_mc_step s i.val coin).getD v.val 0 =
      carpool_step 6 d0 (x,y)
        (if d0 x < d0 y then true else if d0 y < d0 x then false else coin) v := by
  fin_cases i <;> fin_cases v <;> simp [op2130_mc_step, carpool_step] <;> split_ifs <;> simp_all <;> omega

theorem op2130_interval_marginal_recursive_counterexample :
    let f : ℤ → List ℤ → ℕ := fun z d =>
      if d.getD 0 0 + d.getD 1 0 = z then 1 else 0
    let cnt := fun z => op2130_mc_back op2130_mc_example_edges (f z) [0,0,0,0,0,0]
    cnt (-2) = 2904555520 ∧ cnt 0 = 2780823552 ∧ cnt 2 = 2904555520 := by
  have h := op2130_interval_marginal_compressed_counterexample
  exact ⟨(op2130_mc_count_back (-2)).symm.trans h.1,
    (op2130_mc_count_back 0).symm.trans h.2.1,
    (op2130_mc_count_back 2).symm.trans h.2.2⟩
