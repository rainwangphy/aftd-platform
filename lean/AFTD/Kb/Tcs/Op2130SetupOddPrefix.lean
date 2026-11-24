import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130SetupFiniteGadgets
import AFTD.Kb.Tcs.Op2130IntervalMarginalRecursiveCounterexample

/-!
# op2130_setup_odd_prefix

Topic: online_algorithms   Node: ae9dfa474387

Provenance: helper lemma. OP-2130, periodic zero-start decision-circuit preparation

For every k, the explicit zero-start greedy schedule prepares discrepancy prefix [-3,3,5], followed by k copies of [-4,-4,3,5], followed by -3.
-/

def op2130_setup_repeat (offset : ℕ) : ℕ → List (ℕ × Bool)
  | 0 => []
  | k+1 => (op2130_setup_block.map fun (j,c) => (offset+j,c)) ++ op2130_setup_repeat (offset+4) k

def op2130_setup_odd_schedule (k : ℕ) : List (ℕ × Bool) :=
  op2130_setup_pre ++ op2130_setup_repeat 3 k ++
    (op2130_setup_finish.map fun (j,c) => (3+4*k+j,c))


set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem op2130_setup_step_shift (p s : List ℤ) (j : ℕ) (c : Bool) :
    op2130_mc_step (p ++ s) (p.length+j) c = p ++ op2130_mc_step s j c := by
  have h0 : (p ++ s).getD (p.length+j) 0 = s.getD j 0 := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp
  have h1 : (p ++ s).getD (p.length+j+1) 0 = s.getD (j+1) 0 := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hidx : p.length+j+1-p.length = j+1 := by omega
    rw [hidx]
  simp only [op2130_mc_step, h0, h1]
  simp [List.set_append_right, Nat.add_assoc]

theorem op2130_localproof_replay_shift (p s : List ℤ) (ops : List (ℕ × Bool)) :
    op2130_setup_replay (p ++ s) (ops.map fun (j,c) => (p.length+j,c)) =
      p ++ op2130_setup_replay s ops := by
  unfold op2130_setup_replay
  induction ops generalizing s with
  | nil => rfl
  | cons q qs ih =>
      rcases q with ⟨j,c⟩
      simp only [List.map_cons, List.foldl_cons, op2130_setup_step_shift, ih]

theorem op2130_setup_step_append (d s : List ℤ) (j : ℕ) (c : Bool)
    (h : j+1 < d.length) :
    op2130_mc_step (d ++ s) j c = op2130_mc_step d j c ++ s := by
  have h0 : (d ++ s).getD j 0 = d.getD j 0 := by
    exact List.getD_append d s 0 j (by omega)
  have h1 : (d ++ s).getD (j+1) 0 = d.getD (j+1) 0 := by
    exact List.getD_append d s 0 (j+1) h
  simp only [op2130_mc_step, h0, h1]
  rw [List.set_append_left _ _ (by omega)]
  rw [List.set_append_left _ _ (by simp; omega)]

theorem op2130_localproof_replay_append (d s : List ℤ) (ops : List (ℕ × Bool))
    (h : ∀ p ∈ ops, p.1 + 1 < d.length) :
    op2130_setup_replay (d ++ s) ops = op2130_setup_replay d ops ++ s := by
  unfold op2130_setup_replay
  induction ops generalizing d with
  | nil => rfl
  | cons q qs ih =>
      rcases q with ⟨j,c⟩
      simp only [List.foldl_cons]
      rw [op2130_setup_step_append d s j c (h (j,c) (by simp))]
      apply ih
      intro p hp
      have hh := h p (by simp [hp])
      simpa [op2130_mc_step] using hh

def op2130_setup_reservoir : List ℤ := [3,2,1,0,-1,-2,-3,-4,-1]
def op2130_setup_emission : List ℤ := [-4,-4,3,5]

theorem op2130_setup_block_extended (m : ℕ) :
    op2130_setup_replay (op2130_setup_reservoir ++ List.replicate (11+m) 0)
        op2130_setup_block =
      op2130_setup_emission ++ op2130_setup_reservoir ++ List.replicate (7+m) 0 := by
  have hin : op2130_setup_reservoir ++ List.replicate 11 0 =
      [3,2,1,0,-1,-2,-3,-4,-1,0,0,0,0,0,0,0,0,0,0,0] := by decide
  have hout : op2130_setup_emission ++ op2130_setup_reservoir ++ List.replicate 7 0 =
      [-4,-4,3,5,3,2,1,0,-1,-2,-3,-4,-1,0,0,0,0,0,0,0] := by decide
  have hf : op2130_setup_replay (op2130_setup_reservoir ++ List.replicate 11 0)
      op2130_setup_block = op2130_setup_emission ++ op2130_setup_reservoir ++ List.replicate 7 0 := by
    rw [hin, hout]
    exact op2130_setup_finite_gadgets.2.1
  have hb0 : op2130_setup_block.all (fun p => decide (p.1 + 1 < 20)) = true := by decide
  have hb : ∀ p ∈ op2130_setup_block, p.1 + 1 < 20 := by
    intro p hp
    exact of_decide_eq_true ((List.all_eq_true.mp hb0) p hp)
  have hh := op2130_localproof_replay_append
    (op2130_setup_reservoir ++ List.replicate 11 0) (List.replicate m 0)
    op2130_setup_block (by simpa [op2130_setup_reservoir] using hb)
  rw [hf] at hh
  simpa [List.replicate_add, List.append_assoc] using hh

theorem op2130_setup_replay_cat (d : List ℤ) (a b : List (ℕ × Bool)) :
    op2130_setup_replay d (a ++ b) = op2130_setup_replay (op2130_setup_replay d a) b := by
  simp [op2130_setup_replay, List.foldl_append]

theorem op2130_setup_repeat_core (k : ℕ) (p : List ℤ) :
    op2130_setup_replay
      (p ++ op2130_setup_reservoir ++ List.replicate (4*k+11) 0)
      (op2130_setup_repeat p.length k) =
      p ++ (List.replicate k op2130_setup_emission).flatten ++
        op2130_setup_reservoir ++ List.replicate 11 0 := by
  induction k generalizing p with
  | zero => simp [op2130_setup_repeat, op2130_setup_replay]
  | succ k ih =>
      simp only [op2130_setup_repeat, op2130_setup_replay_cat]
      rw [show 4 * (k+1) + 11 = 11 + (4*k+4) by omega]
      have hshift := op2130_localproof_replay_shift p
        (op2130_setup_reservoir ++ List.replicate (11+(4*k+4)) 0) op2130_setup_block
      have hmap : (op2130_setup_block.map fun (j,c) => (p.length+j,c)) =
          (op2130_setup_block.map fun q => (p.length+q.1,q.2)) := by
        congr 1
      rw [hmap] at hshift
      rw [List.append_assoc p op2130_setup_reservoir]
      rw [hshift, op2130_setup_block_extended]
      have hh := ih (p ++ op2130_setup_emission)
      simp only [List.length_append] at hh
      have hl : op2130_setup_emission.length = 4 := by decide
      rw [hl] at hh
      have hz : 7 + (4*k+4) = 4*k+11 := by omega
      rw [hz]
      simpa [List.append_assoc, List.replicate_succ] using hh

theorem op2130_setup_pre_extended (m : ℕ) :
    op2130_setup_replay (List.replicate (23+m) 0) op2130_setup_pre =
      ([-3,3,5] : List ℤ) ++ op2130_setup_reservoir ++ List.replicate (11+m) 0 := by
  have hout : ([-3,3,5] : List ℤ) ++ op2130_setup_reservoir ++ List.replicate 11 0 =
      [-3,3,5,3,2,1,0,-1,-2,-3,-4,-1,0,0,0,0,0,0,0,0,0,0,0] := by decide
  have hf : op2130_setup_replay (List.replicate 23 0) op2130_setup_pre =
      ([-3,3,5] : List ℤ) ++ op2130_setup_reservoir ++ List.replicate 11 0 := by
    rw [hout]
    exact op2130_setup_finite_gadgets.1
  have hb0 : op2130_setup_pre.all (fun p => decide (p.1 + 1 < 23)) = true := by decide
  have hb : ∀ p ∈ op2130_setup_pre, p.1 + 1 < (List.replicate 23 (0:ℤ)).length := by
    intro p hp
    simpa using of_decide_eq_true ((List.all_eq_true.mp hb0) p hp)
  have hh := op2130_localproof_replay_append (List.replicate 23 0) (List.replicate m 0)
    op2130_setup_pre hb
  rw [hf] at hh
  simpa [List.replicate_add, List.append_assoc] using hh

theorem op2130_setup_finish_head :
    (op2130_setup_replay (op2130_setup_reservoir ++ List.replicate 11 0)
      op2130_setup_finish).take 1 = [-3] := by
  have hin : op2130_setup_reservoir ++ List.replicate 11 0 =
      [3,2,1,0,-1,-2,-3,-4,-1,0,0,0,0,0,0,0,0,0,0,0] := by decide
  rw [hin, op2130_setup_finite_gadgets.2.2]
  decide

theorem op2130_setup_emission_length (k : ℕ) :
    ((List.replicate k op2130_setup_emission).flatten).length = 4*k := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, op2130_setup_emission, ih]; omega

theorem op2130_setup_odd_prefix (k : ℕ) :
  (op2130_setup_replay (List.replicate (4*k+23) 0) (op2130_setup_odd_schedule k)).take (4*k+4) =
    ([-3,3,5] ++ (List.replicate k ([-4,-4,3,5] : List ℤ)).flatten ++ [-3]) := by
  unfold op2130_setup_odd_schedule
  rw [op2130_setup_replay_cat, op2130_setup_replay_cat]
  have hsize : 4*k+23 = 23+4*k := by omega
  rw [hsize, op2130_setup_pre_extended]
  have hr := op2130_setup_repeat_core k ([-3,3,5] : List ℤ)
  simp only [List.length_cons, List.length_nil] at hr
  have hz : 11+4*k = 4*k+11 := by omega
  rw [hz, hr]
  let p : List ℤ := [-3,3,5] ++ (List.replicate k op2130_setup_emission).flatten
  have plen : p.length = 3+4*k := by
    simp [p, op2130_setup_emission]
    omega
  have hshift := op2130_localproof_replay_shift p
    (op2130_setup_reservoir ++ List.replicate 11 0) op2130_setup_finish
  rw [plen] at hshift
  have hmap : (op2130_setup_finish.map fun (j,c) => (3+4*k+j,c)) =
      (op2130_setup_finish.map fun q => (3+4*k+q.1,q.2)) := by congr 1
  rw [hmap] at hshift
  rw [hmap]
  have hstate : ([-3,3,5] : List ℤ) ++ (List.replicate k op2130_setup_emission).flatten ++
      op2130_setup_reservoir ++ List.replicate 11 0 =
      p ++ (op2130_setup_reservoir ++ List.replicate 11 0) := by
    simp [p, List.append_assoc]
  rw [hstate, hshift]
  have htake : 4*k+4 = p.length+1 := by rw [plen]; omega
  rw [htake, List.take_append]
  rw [List.take_of_length_le (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [op2130_setup_finish_head]
  simp [p, op2130_setup_emission, List.append_assoc]
