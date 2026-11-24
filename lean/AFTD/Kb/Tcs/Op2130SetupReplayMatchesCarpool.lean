import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130SetupFiniteGadgets
import AFTD.Kb.Tcs.Op2130PathPrefixDiscrepanciesCoinMonotone
import AFTD.Kb.Tcs.CarpoolStep
import AFTD.Kb.Tcs.CarpoolGreedyOrientations
import AFTD.Kb.Tcs.CarpoolDiscrepancies
import AFTD.Kb.Tcs.Op2130IntervalMarginalRecursiveCounterexample

/-!
# op2130_setup_replay_matches_carpool

Topic: online_algorithms   Node: 2e4fa5d3ecef

Provenance: helper lemma. OP-2130, lifting the list-state preparation into the existing path process

For every valid list of path-edge indices and coin bits, replaying the list-state greedy updates from zero agrees with the repository carpool discrepancies at every terminal vertex.
-/

set_option maxHeartbeats 2000000

theorem op2130_mc_step_agrees_local (n : ℕ) (d : List ℤ) (hd : d.length = n)
    (j : ℕ) (hj : j+1 < n) (c : Bool) (v : Fin n) :
    let D : Fin n → ℤ := fun i => d.getD i.val 0
    let a : Fin n := ⟨j, by omega⟩
    let b : Fin n := ⟨j+1, hj⟩
    (op2130_mc_step d j c).getD v.val 0 =
      carpool_step n D (a,b) (if D a < D b then true else if D b < D a then false else c) v := by
  have h0 : j < d.length := by omega
  have h1 : j+1 < d.length := by omega
  by_cases hv0 : v.val = j
  · have hv1 : v.val ≠ j+1 := by omega
    simp [op2130_mc_step, carpool_step, List.getD_eq_getElem?_getD,
      List.getElem?_set, Fin.ext_iff, hv0, hv1, h0, h1] <;> split_ifs <;> simp_all <;> omega
  · by_cases hv1 : v.val = j+1
    · simp [op2130_mc_step, carpool_step, List.getD_eq_getElem?_getD,
        List.getElem?_set, Fin.ext_iff, hv0, hv1, h0, h1] <;> split_ifs <;> simp_all <;> omega
    · simp [op2130_mc_step, carpool_step, List.getD_eq_getElem?_getD,
        List.getElem?_set, Fin.ext_iff, hv0, hv1, Ne.symm hv0, Ne.symm hv1, h0, h1]


def op2130_edge_of_nat (n : ℕ) (hn : 0 < n) (j : ℕ) : Fin n × Fin n :=
  (⟨j % n, Nat.mod_lt _ hn⟩, ⟨(j+1) % n, Nat.mod_lt _ hn⟩)

def op2130_aux_run (n : ℕ) (es : List (Fin n × Fin n)) (cs : List Bool)
    (d : Fin n → ℤ) : Fin n → ℤ :=
  (es.zip (carpool_greedy_orientations.aux n es cs d)).foldl
    (fun v (e,b) => carpool_step n v e b) d

theorem op2130_aux_run_cons (n : ℕ) (e : Fin n × Fin n) (es : List (Fin n × Fin n))
    (c : Bool) (cs : List Bool) (d : Fin n → ℤ) :
    op2130_aux_run n (e::es) (c::cs) d =
      op2130_aux_run n es cs (carpool_step n d e
        (if d e.1 < d e.2 then true else if d e.2 < d e.1 then false else c)) := by
  unfold op2130_aux_run
  rw [carpool_greedy_orientations.aux.eq_def]
  simp only [List.zip_cons_cons, List.foldl_cons]

theorem op2130_list_replay_aux_match (n : ℕ) (hn : 0 < n) (ops : List (ℕ × Bool))
    (hvalid : ∀ p ∈ ops, p.1+1 < n) (d : List ℤ) (hd : d.length = n) (v : Fin n) :
    op2130_aux_run n (ops.map fun p => op2130_edge_of_nat n hn p.1) (ops.map Prod.snd)
      (fun i => d.getD i.val 0) v = (op2130_setup_replay d ops).getD v.val 0 := by
  induction ops generalizing d with
  | nil => simp [op2130_aux_run, op2130_setup_replay]
  | cons q qs ih =>
      rcases q with ⟨j,c⟩
      have hj : j+1 < n := hvalid (j,c) (by simp)
      have hqs : ∀ p ∈ qs, p.1+1 < n := by
        intro p hp
        exact hvalid p (by simp [hp])
      simp only [List.map_cons, List.foldl_cons, op2130_setup_replay]
      rw [op2130_aux_run_cons]
      have hmod0 : j % n = j := Nat.mod_eq_of_lt (by omega)
      have hmod1 : (j+1) % n = j+1 := Nat.mod_eq_of_lt hj
      have hstep : carpool_step n (fun i => d.getD i.val 0) (op2130_edge_of_nat n hn j)
          (if d.getD (op2130_edge_of_nat n hn j).1.val 0 < d.getD (op2130_edge_of_nat n hn j).2.val 0 then true else
            if d.getD (op2130_edge_of_nat n hn j).2.val 0 < d.getD (op2130_edge_of_nat n hn j).1.val 0 then false else c) =
          (fun i => (op2130_mc_step d j c).getD i.val 0) := by
        funext i
        simpa [op2130_edge_of_nat, hmod0, hmod1] using (op2130_mc_step_agrees_local n d hd j hj c i).symm
      rw [hstep]
      apply ih hqs
      simp [op2130_mc_step, hd]

theorem op2130_aux_length (n : ℕ) (es : List (Fin n × Fin n)) (cs : List Bool)
    (d : Fin n → ℤ) (h : es.length = cs.length) :
    (carpool_greedy_orientations.aux n es cs d).length = es.length := by
  induction es generalizing cs d with
  | nil => simp [carpool_greedy_orientations.aux.eq_def]
  | cons e es ih =>
      cases cs with
      | nil => simp at h
      | cons c cs =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          rw [carpool_greedy_orientations.aux.eq_def]
          simp only [List.length_cons]
          exact congrArg Nat.succ (ih cs _ h)

theorem op2130_scanl_terminal {α β : Type} (f : β → α → β)
    (xs : List α) (b fallback : β) :
    (xs.scanl f b).getD xs.length fallback = xs.foldl f b := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih => simp [List.scanl_cons, List.foldl_cons, ih]

theorem op2130_carpool_terminal_aux (n : ℕ) (es : List (Fin n × Fin n))
    (cs : List Bool) (h : es.length = cs.length) :
    (carpool_discrepancies n es (carpool_greedy_orientations n es cs)).getD
      es.length (fun _ => 0) = op2130_aux_run n es cs (fun _ => 0) := by
  have ha := op2130_aux_length n es cs (fun _ => 0) h
  unfold carpool_discrepancies carpool_greedy_orientations op2130_aux_run
  have hz : (es.zip (carpool_greedy_orientations.aux n es cs (fun _ => 0))).length = es.length := by
    simp [ha]
  rw [← hz]
  exact op2130_scanl_terminal _ _ _ _

theorem op2130_setup_replay_matches_carpool (n : ℕ) (hn : 0 < n) (ops : List (ℕ × Bool)) (hvalid : ∀ p ∈ ops, p.1+1 < n) (v : Fin n) :
 let es : List (Fin n × Fin n) := ops.map fun (j,_) => (⟨j % n, Nat.mod_lt _ hn⟩, ⟨(j+1) % n, Nat.mod_lt _ hn⟩)
 let cs : List Bool := ops.map Prod.snd
 ((carpool_discrepancies n es (carpool_greedy_orientations n es cs)).getD es.length (fun _ => 0)) v =
   (op2130_setup_replay (List.replicate n 0) ops).getD v.val 0 := by
  let es := ops.map fun p => op2130_edge_of_nat n hn p.1
  let cs := ops.map Prod.snd
  have hlen : es.length = cs.length := by simp [es,cs]
  have hterm := op2130_carpool_terminal_aux n es cs hlen
  have hrun := op2130_list_replay_aux_match n hn ops hvalid (List.replicate n 0) (by simp) v
  have hzero : (fun i : Fin n => (List.replicate n (0:ℤ)).getD i.val 0) = (fun _ => 0) := by
    funext i
    exact List.getD_replicate 0 i.isLt
  rw [hzero] at hrun
  change ((carpool_discrepancies n es (carpool_greedy_orientations n es cs)).getD es.length (fun _ => 0)) v = _
  rw [hterm]
  exact hrun
