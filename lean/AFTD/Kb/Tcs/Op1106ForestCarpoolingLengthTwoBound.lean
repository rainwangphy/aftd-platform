import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolForestEdgeSequence
import AFTD.Kb.Tcs.CarpoolGreedyOrientations
import AFTD.Kb.Tcs.CarpoolMaxDiscrepancy
import AFTD.Kb.Tcs.MaxVertexDiscrepancy
import AFTD.Kb.Tcs.CarpoolStep
import AFTD.Kb.Tcs.ValidCarpoolEdgeSequence
import AFTD.Kb.Tcs.CarpoolDiscrepancies

/-!
# op_1106_forest_carpooling_length_two_bound

Topic: online_algorithms   Node: 94d83687b728

Provenance: helper lemma. arXiv:2611.00388: Online carpooling against an oblivious adversary; OP-1106

For any oblivious forest edge sequence of length 2 on Fin n and any assignment of 2 coins, the maximum prefix discrepancy under randomized greedy carpooling is at most 1.
-/

lemma op_1106_carpool_step_not_mem (n : ℕ) (d : Fin n → ℤ) (e : Fin n × Fin n) (b : Bool) (v : Fin n)
    (h1 : v ≠ e.1) (h2 : v ≠ e.2) :
    carpool_step n d e b v = d v := by
  dsimp [carpool_step]
  rw [if_neg h1, if_neg h2]
  ring

lemma op_1106_carpool_step_fst (n : ℕ) (d : Fin n → ℤ) (e : Fin n × Fin n) (he : e.1 ≠ e.2) (b : Bool) :
    carpool_step n d e b e.1 = d e.1 + if b then 1 else -1 := by
  dsimp [carpool_step]
  rw [if_pos rfl, if_neg he]
  ring

lemma op_1106_carpool_step_snd (n : ℕ) (d : Fin n → ℤ) (e : Fin n × Fin n) (he : e.1 ≠ e.2) (b : Bool) :
    carpool_step n d e b e.2 = d e.2 + if b then -1 else 1 := by
  dsimp [carpool_step]
  rw [if_neg (Ne.symm he), if_pos rfl]
  ring

lemma op_1106_carpool_greedy_two (n : ℕ) (e1 e2 : Fin n × Fin n) (c1 c2 : Bool) :
    carpool_greedy_orientations n [e1, e2] [c1, c2] =
      let b1 := c1
      let d1 := carpool_step n (fun _ => 0) e1 b1
      let b2 := if d1 e2.1 < d1 e2.2 then true else if d1 e2.2 < d1 e2.1 then false else c2
      [b1, b2] := by
  unfold carpool_greedy_orientations
  rw [carpool_greedy_orientations.aux.eq_def]
  dsimp only
  have h1 : ¬ ((0 : ℤ) < 0) := by decide
  change (if (0 : ℤ) < 0 then true else if (0 : ℤ) < 0 then false else c1) :: _ = _
  rw [if_neg h1, if_neg h1]
  congr 1

lemma op_1106_carpool_max_discrepancy_two (n : ℕ) (e1 e2 : Fin n × Fin n) (b1 b2 : Bool) :
    carpool_max_discrepancy n [e1, e2] [b1, b2] =
      max (max (max 0 (max_vertex_discrepancy n (fun _ => 0)))
               (max_vertex_discrepancy n (carpool_step n (fun _ => 0) e1 b1)))
          (max_vertex_discrepancy n (carpool_step n (carpool_step n (fun _ => 0) e1 b1) e2 b2)) := by
  dsimp [carpool_max_discrepancy, carpool_discrepancies]
  rfl

lemma op_1106_carpool_step_zero_bounds (n : ℕ) (e : Fin n × Fin n) (b : Bool) (v : Fin n) :
    -1 ≤ carpool_step n (fun _ => 0) e b v ∧ carpool_step n (fun _ => 0) e b v ≤ 1 := by
  dsimp [carpool_step]
  split_ifs <;> omega

lemma op_1106_carpool_step_zero_not_both_one (n : ℕ) (e : Fin n × Fin n) (he : e.1 ≠ e.2) (b : Bool)
    (u v : Fin n) (huv : u ≠ v) :
    ¬ (carpool_step n (fun _ => 0) e b u = 1 ∧ carpool_step n (fun _ => 0) e b v = 1) := by
  dsimp [carpool_step]
  intro ⟨h1, h2⟩
  split_ifs at h1 h2 <;> (try subst_vars) <;> (try contradiction)

lemma op_1106_carpool_step_zero_not_both_neg_one (n : ℕ) (e : Fin n × Fin n) (he : e.1 ≠ e.2) (b : Bool)
    (u v : Fin n) (huv : u ≠ v) :
    ¬ (carpool_step n (fun _ => 0) e b u = -1 ∧ carpool_step n (fun _ => 0) e b v = -1) := by
  dsimp [carpool_step]
  intro ⟨h1, h2⟩
  split_ifs at h1 h2 <;> (try subst_vars) <;> (try contradiction)

lemma op_1106_carpool_greedy_step_bounded (x y : ℤ) (c : Bool)
    (hx1 : -1 ≤ x) (hx2 : x ≤ 1)
    (hy1 : -1 ≤ y) (hy2 : y ≤ 1)
    (hnot_both_pos : ¬(x = 1 ∧ y = 1))
    (hnot_both_neg : ¬(x = -1 ∧ y = -1)) :
    let b := if x < y then true else if y < x then false else c
    (x + (if b then 1 else -1)).natAbs ≤ 1 ∧
    (y + (if b then -1 else 1)).natAbs ≤ 1 := by
  rcases c with _ | _ <;>
    interval_cases x <;> interval_cases y <;>
    intro b <;>
    dsimp [b] <;>
    first
    | (exfalso; apply hnot_both_pos; decide)
    | (exfalso; apply hnot_both_neg; decide)
    | (revert b; decide)

/-- On any forest edge sequence of length 2, randomized greedy carpooling achieves maximum discrepancy at most 1 for any coin assignment. -/
theorem op_1106_forest_carpooling_length_two_bound
    (n : ℕ) (edges : List (Fin n × Fin n))
    (hT : edges.length = 2)
    (hforest : CarpoolForestEdgeSequence n edges)
    (coins : List Bool) (hcoins : coins.length = 2) :
    carpool_max_discrepancy n edges (carpool_greedy_orientations n edges coins) ≤ 1 := by
  match edges, coins, hT, hcoins with
  | [e1, e2], [c1, c2], _, _ =>
    have he1 : e1.1 ≠ e1.2 := hforest.1 e1 (by simp)
    have he2 : e2.1 ≠ e2.2 := hforest.1 e2 (by simp)
    rw [op_1106_carpool_greedy_two]
    dsimp only
    rw [op_1106_carpool_max_discrepancy_two]
    simp only [max_le_iff]
    refine ⟨⟨⟨by norm_num, ?_⟩, ?_⟩, ?_⟩
    · unfold max_vertex_discrepancy
      apply Finset.sup_le
      intro v _
      norm_num
    · unfold max_vertex_discrepancy
      apply Finset.sup_le
      intro v _
      have hb := op_1106_carpool_step_zero_bounds n e1 c1 v
      omega
    · unfold max_vertex_discrepancy
      apply Finset.sup_le
      intro v _
      set d1 := carpool_step n (fun _ => 0) e1 c1
      set b2 := if d1 e2.1 < d1 e2.2 then true else if d1 e2.2 < d1 e2.1 then false else c2
      have hx_bounds := op_1106_carpool_step_zero_bounds n e1 c1 e2.1
      have hy_bounds := op_1106_carpool_step_zero_bounds n e1 c1 e2.2
      have hnot_pos := op_1106_carpool_step_zero_not_both_one n e1 he1 c1 e2.1 e2.2 he2
      have hnot_neg := op_1106_carpool_step_zero_not_both_neg_one n e1 he1 c1 e2.1 e2.2 he2
      have hstep := op_1106_carpool_greedy_step_bounded (d1 e2.1) (d1 e2.2) c2
        hx_bounds.1 hx_bounds.2 hy_bounds.1 hy_bounds.2 hnot_pos hnot_neg
      by_cases hv1 : v = e2.1
      · subst hv1
        rw [op_1106_carpool_step_fst n d1 e2 he2 b2]
        exact hstep.1
      · by_cases hv2 : v = e2.2
        · subst hv2
          rw [op_1106_carpool_step_snd n d1 e2 he2 b2]
          exact hstep.2
        · rw [op_1106_carpool_step_not_mem n d1 e2 b2 v hv1 hv2]
          dsimp [d1]
          have hb := op_1106_carpool_step_zero_bounds n e1 c1 v
          omega
