import AFTD.Prelude
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.DiscreteDist
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.IsPartiallyAdaptive
import AFTD.Kb.Tcs.ExpectedUtilityDUS
import AFTD.Kb.Tcs.PandoraIsReservation
import AFTD.Kb.Tcs.PandoraCappedSurplus
import AFTD.Kb.Tcs.PandoraThresholdPolicy
import AFTD.Kb.Tcs.Support

/-!
# pandora_threshold_policy_lower_bound

Topic: online_algorithms   Node: 99c2ba05a8cd

Provenance: helper lemma. Helper for op184_partially_adaptive_half_approximation: arXiv:2610.13775 Section 3, Lemma 3 (threshold-surplus lower bound), with deferred-until-stopping commitment, which only helps

Lemma 3: for reservation values r, t >= 0 and a duplicate-free list of boxes each with positive capped surplus at t, the threshold policy has expected DUS utility at least min(t, total capped surplus of the list).
-/

lemma pandora_threshold_policy_lower_bound_foldl_max {α : Type*} (history : List (α × ℝ)) (acc v : ℝ) :
    history.foldl (fun a bv => max a bv.2) (max acc v) =
      max (history.foldl (fun a bv => max a bv.2) acc) v := by
  induction history generalizing acc with
  | nil => rfl
  | cons head tail ih =>
    show List.foldl (fun a bv => max a bv.2) (max (max acc v) head.2) tail =
      max (List.foldl (fun a bv => max a bv.2) (max acc head.2) tail) v
    have : max (max acc v) head.2 = max (max acc head.2) v := by
      rw [max_assoc, max_comm v, ← max_assoc]
    rw [this, ih]

def pandora_threshold_policy_lower_bound_history_max {n : ℕ} (history : List (Fin n × ℝ)) : ℝ :=
  history.foldl (fun acc bv => max acc bv.2) 0

lemma pandora_threshold_policy_lower_bound_history_max_cons {n : ℕ} (b : Fin n) (v : ℝ) (history : List (Fin n × ℝ)) :
    pandora_threshold_policy_lower_bound_history_max ((b, v) :: history) =
      max (pandora_threshold_policy_lower_bound_history_max history) v := by
  show List.foldl (fun a bv => max a bv.2) (max 0 v) history = _
  exact pandora_threshold_policy_lower_bound_foldl_max history 0 v

lemma pandora_threshold_policy_lower_bound_foldl_max_nonneg {α : Type*} (history : List (α × ℝ)) (acc : ℝ) (hacc : 0 ≤ acc) :
    0 ≤ history.foldl (fun a bv => max a bv.2) acc := by
  induction history generalizing acc with
  | nil => exact hacc
  | cons head tail ih =>
    apply ih
    exact le_trans hacc (le_max_left acc head.2)

lemma pandora_threshold_policy_lower_bound_history_max_nonneg {n : ℕ} (history : List (Fin n × ℝ)) :
    0 ≤ pandora_threshold_policy_lower_bound_history_max history :=
  pandora_threshold_policy_lower_bound_foldl_max_nonneg history 0 le_rfl

lemma pandora_threshold_policy_lower_bound_pointwise_comb (v r t U : ℝ) (htr : t ≤ r) :
    (if t < v then v else U) - max (v - r) 0 =
      (if t < v then t else 0) + max (min v r - t) 0 + (if t < v then 0 else U) := by
  have hid : (if t < v then v else U) = (if t < v then v else 0) + (if t < v then 0 else U) := by
    split_ifs <;> ring
  rw [hid]
  have h1 : (if t < v then v else 0) - max (v - r) 0 =
      (if t < v then t else 0) + max (min v r - t) 0 := by
    split_ifs with h
    · rcases le_total v r with hvr | hrv
      · have h2 : v - r ≤ 0 := by linarith
        rw [max_eq_right h2, min_eq_left hvr]
        have h3 : 0 ≤ v - t := by linarith
        rw [max_eq_left h3]; ring
      · have h2 : (0 : ℝ) ≤ v - r := by linarith
        rw [max_eq_left h2, min_eq_right hrv]
        have h3 : (0 : ℝ) ≤ r - t := by linarith
        rw [max_eq_left h3]; ring
    · have hle : v ≤ t := not_lt.mp h
      have hvr : v ≤ r := hle.trans htr
      have h2 : v - r ≤ 0 := by linarith
      have h3 : min v r - t ≤ 0 := by linarith [min_le_left v r]
      rw [max_eq_right h2, max_eq_right h3]; ring
  linarith

lemma pandora_threshold_policy_lower_bound_sum_indicator_prop (dist : DiscreteDist) (t U : ℝ) :
    let p := ∑ v ∈ dist.support, dist.prob v * (if t < v then (1 : ℝ) else 0)
    (∑ v ∈ dist.support, dist.prob v * (if t < v then t else 0)) = p * t ∧
    (∑ v ∈ dist.support, dist.prob v * (if t < v then 0 else U)) = (1 - p) * U ∧
    0 ≤ p := by
  intro p
  have hp_nonneg : 0 ≤ p := by
    apply Finset.sum_nonneg
    intro v hv
    have : 0 ≤ (if t < v then (1 : ℝ) else 0) := by split_ifs <;> linarith
    exact mul_nonneg (dist.prob_nonneg v hv) this
  have h1 : (∑ v ∈ dist.support, dist.prob v * (if t < v then t else 0)) = p * t := by
    dsimp [p]
    have hid : ∀ v ∈ dist.support, dist.prob v * (if t < v then t else 0) =
        (dist.prob v * (if t < v then 1 else 0)) * t := by
      intro v _
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hid, ← Finset.sum_mul]
  have h2 : (∑ v ∈ dist.support, dist.prob v * (if t < v then 0 else U)) = (1 - p) * U := by
    dsimp [p]
    have hid : ∀ v ∈ dist.support, dist.prob v * (if t < v then 0 else U) =
        (dist.prob v - dist.prob v * (if t < v then 1 else 0)) * U := by
      intro v _
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hid, ← Finset.sum_mul, Finset.sum_sub_distrib, dist.sum_prob_one]
  exact ⟨h1, h2, hp_nonneg⟩

lemma pandora_threshold_policy_lower_bound_sum_pointwise_comb (dist : DiscreteDist) (c r t U : ℝ) (htr : t ≤ r)
    (hres : ∑ v ∈ dist.support, dist.prob v * max (v - r) 0 = c) :
    let p := ∑ v ∈ dist.support, dist.prob v * (if t < v then (1 : ℝ) else 0)
    (∑ v ∈ dist.support, dist.prob v * (if t < v then v else U)) - c =
      p * t + (∑ v ∈ dist.support, dist.prob v * max (min v r - t) 0) + (1 - p) * U := by
  intro p
  have h_id : ∀ v ∈ dist.support,
      dist.prob v * (if t < v then v else U) - dist.prob v * max (v - r) 0 =
        dist.prob v * (if t < v then t else 0) +
        dist.prob v * max (min v r - t) 0 +
        dist.prob v * (if t < v then 0 else U) := by
    intro v _
    have h := pandora_threshold_policy_lower_bound_pointwise_comb v r t U htr
    calc dist.prob v * (if t < v then v else U) - dist.prob v * max (v - r) 0
      _ = dist.prob v * ((if t < v then v else U) - max (v - r) 0) := by ring
      _ = dist.prob v * ((if t < v then t else 0) + max (min v r - t) 0 + (if t < v then 0 else U)) := by rw [h]
      _ = dist.prob v * (if t < v then t else 0) +
          dist.prob v * max (min v r - t) 0 +
          dist.prob v * (if t < v then 0 else U) := by ring
  have h_sub : (∑ v ∈ dist.support, dist.prob v * (if t < v then v else U)) - c =
      ∑ v ∈ dist.support, (dist.prob v * (if t < v then v else U) - dist.prob v * max (v - r) 0) := by
    rw [← hres, Finset.sum_sub_distrib]
  rw [h_sub]
  have h_sum_id : (∑ v ∈ dist.support, (dist.prob v * (if t < v then v else U) - dist.prob v * max (v - r) 0)) =
      (∑ v ∈ dist.support, dist.prob v * (if t < v then t else 0)) +
      (∑ v ∈ dist.support, dist.prob v * max (min v r - t) 0) +
      (∑ v ∈ dist.support, dist.prob v * (if t < v then 0 else U)) := by
    rw [Finset.sum_congr rfl h_id]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [h_sum_id]
  have hp_eq : (∑ v ∈ dist.support, dist.prob v * (if t < v then t else 0)) = p * t :=
    (pandora_threshold_policy_lower_bound_sum_indicator_prop dist t U).1
  have hp_eq2 : (∑ v ∈ dist.support, dist.prob v * (if t < v then 0 else U)) = (1 - p) * U :=
    (pandora_threshold_policy_lower_bound_sum_indicator_prop dist t U).2.1
  rw [hp_eq, hp_eq2]

lemma pandora_threshold_policy_lower_bound_convex_min_ineq (p t w W : ℝ) (hp : 0 ≤ p) (hw : 0 ≤ w) :
    min t (w + W) ≤ p * t + w + (1 - p) * min t W := by
  rcases le_total t W with htW | hWt
  · rw [min_eq_left htW]
    have : min t (w + W) ≤ t := min_le_left t (w + W)
    have : t ≤ p * t + w + (1 - p) * t := by
      calc t = p * t + (1 - p) * t := by ring
      _ ≤ p * t + (1 - p) * t + w := by linarith
      _ = p * t + w + (1 - p) * t := by ring
    linarith
  · rw [min_eq_right hWt]
    have : min t (w + W) ≤ w + W := min_le_right t (w + W)
    have : w + W ≤ p * t + w + (1 - p) * W := by
      have : p * W ≤ p * t := mul_le_mul_of_nonneg_left hWt hp
      linarith
    linarith

lemma pandora_threshold_policy_lower_bound_le_r_of_capped_surplus_pos (inst : PandoraDeadlineInstance) (r : Fin inst.n → ℝ)
    (i : Fin inst.n) (t : ℝ) (hpos : 0 < pandora_capped_surplus inst r i t) : t ≤ r i := by
  by_contra! h
  have hzero : pandora_capped_surplus inst r i t ≤ 0 := by
    unfold pandora_capped_surplus
    apply Finset.sum_nonpos
    intro v hv
    have h1 : min v (r i) - t ≤ 0 := by linarith [min_le_right v (r i)]
    rw [max_eq_right h1]
    simp
  linarith

lemma pandora_threshold_policy_lower_bound_aux (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (hr : pandora_is_reservation inst r) (t : ℝ) (_ht : 0 ≤ t)
    (order : List (Fin inst.n)) (hnd : order.Nodup)
    (hpos : ∀ i ∈ order, 0 < pandora_capped_surplus inst r i t)
    (history : List (Fin inst.n × ℝ)) (hH : pandora_threshold_policy_lower_bound_history_max history ≤ t) :
    min t (∑ i ∈ order.toFinset, pandora_capped_surplus inst r i t) ≤
      expectedUtilityDUS.aux inst history (pandora_threshold_policy order t) := by
  induction order generalizing history with
  | nil =>
    have hnil : pandora_threshold_policy ([] : List (Fin inst.n)) t = AdaptivePolicy.stop := rfl
    rw [hnil]
    have haux : expectedUtilityDUS.aux inst history AdaptivePolicy.stop =
        pandora_threshold_policy_lower_bound_history_max history := rfl
    rw [haux]
    simp only [List.toFinset_nil, Finset.sum_empty]
    have : min t 0 ≤ 0 := min_le_right t 0
    have : 0 ≤ pandora_threshold_policy_lower_bound_history_max history :=
      pandora_threshold_policy_lower_bound_history_max_nonneg history
    linarith
  | cons b rest ih =>
    have hb_notin : b ∉ rest := (List.nodup_cons.mp hnd).1
    have hnd_rest : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hpos_b : 0 < pandora_capped_surplus inst r b t := hpos b (List.Mem.head rest)
    have hpos_rest : ∀ i ∈ rest, 0 < pandora_capped_surplus inst r i t :=
      fun i hi => hpos i (List.Mem.tail b hi)
    have htr : t ≤ r b := pandora_threshold_policy_lower_bound_le_r_of_capped_surplus_pos inst r b t hpos_b
    have hw_nonneg : 0 ≤ pandora_capped_surplus inst r b t := le_of_lt hpos_b
    have hnotin_toFinset : b ∉ rest.toFinset := by
      rw [List.mem_toFinset]
      exact hb_notin
    have h_sum : (∑ i ∈ (b :: rest).toFinset, pandora_capped_surplus inst r i t) =
        pandora_capped_surplus inst r b t + ∑ i ∈ rest.toFinset, pandora_capped_surplus inst r i t := by
      rw [List.toFinset_cons, Finset.sum_insert hnotin_toFinset]
    rw [h_sum]
    set w := pandora_capped_surplus inst r b t
    set W := ∑ i ∈ rest.toFinset, pandora_capped_surplus inst r i t
    set U := min t W
    set p := ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v * (if t < v then (1 : ℝ) else 0)
    have hp_nonneg : 0 ≤ p := (pandora_threshold_policy_lower_bound_sum_indicator_prop (inst.dist b) t U).2.2
    have h_convex : min t (w + W) ≤ p * t + w + (1 - p) * U :=
      pandora_threshold_policy_lower_bound_convex_min_ineq p t w W hp_nonneg hw_nonneg
    have h_res : (∑ v ∈ (inst.dist b).support, (inst.dist b).prob v * max (v - r b) 0) = inst.cost b :=
      hr b
    have h_comb := pandora_threshold_policy_lower_bound_sum_pointwise_comb (inst.dist b) (inst.cost b) (r b) t U htr h_res
    change (∑ v ∈ (inst.dist b).support, (inst.dist b).prob v * (if t < v then v else U)) - inst.cost b =
      p * t + w + (1 - p) * U at h_comb
    rw [← h_comb] at h_convex
    have h_pointwise : ∀ v ∈ (inst.dist b).support,
        (if t < v then v else U) ≤
          expectedUtilityDUS.aux inst ((b, v) :: history)
            (if t < v then AdaptivePolicy.stop else pandora_threshold_policy rest t) := by
      intro v _
      split_ifs with htv
      · have haux : expectedUtilityDUS.aux inst ((b, v) :: history) AdaptivePolicy.stop =
            pandora_threshold_policy_lower_bound_history_max ((b, v) :: history) := rfl
        rw [haux, pandora_threshold_policy_lower_bound_history_max_cons]
        exact le_max_right (pandora_threshold_policy_lower_bound_history_max history) v
      · have hle : v ≤ t := not_lt.mp htv
        have hH_new : pandora_threshold_policy_lower_bound_history_max ((b, v) :: history) ≤ t := by
          rw [pandora_threshold_policy_lower_bound_history_max_cons]
          exact max_le hH hle
        exact ih hnd_rest hpos_rest ((b, v) :: history) hH_new
    have h_sum_le :
        (∑ v ∈ (inst.dist b).support, (inst.dist b).prob v * (if t < v then v else U)) ≤
        (∑ v ∈ (inst.dist b).support, (inst.dist b).prob v *
          expectedUtilityDUS.aux inst ((b, v) :: history)
            (if t < v then AdaptivePolicy.stop else pandora_threshold_policy rest t)) := by
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_mul_of_nonneg_left (h_pointwise v hv) ((inst.dist b).prob_nonneg v hv)
    have h_pol : pandora_threshold_policy (b :: rest) t =
        AdaptivePolicy.openBox b (fun v => if t < v then AdaptivePolicy.stop else pandora_threshold_policy rest t) := rfl
    rw [h_pol]
    have haux_open : expectedUtilityDUS.aux inst history
        (AdaptivePolicy.openBox b (fun v => if t < v then AdaptivePolicy.stop else pandora_threshold_policy rest t)) =
        (∑ v ∈ (inst.dist b).support, (inst.dist b).prob v *
          expectedUtilityDUS.aux inst ((b, v) :: history)
            (if t < v then AdaptivePolicy.stop else pandora_threshold_policy rest t)) - inst.cost b := rfl
    rw [haux_open]
    linarith

theorem pandora_threshold_policy_lower_bound (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (hr : pandora_is_reservation inst r) (t : ℝ) (ht : 0 ≤ t)
    (order : List (Fin inst.n)) (hnd : order.Nodup)
    (hpos : ∀ i ∈ order, 0 < pandora_capped_surplus inst r i t) :
    min t (∑ i ∈ order.toFinset, pandora_capped_surplus inst r i t) ≤
      expectedUtilityDUS inst (pandora_threshold_policy order t) := by
  have hH : pandora_threshold_policy_lower_bound_history_max ([] : List (Fin inst.n × ℝ)) ≤ t := by
    change 0 ≤ t
    exact ht
  exact pandora_threshold_policy_lower_bound_aux inst r hr t ht order hnd hpos [] hH
