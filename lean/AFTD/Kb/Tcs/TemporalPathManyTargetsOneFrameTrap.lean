import AFTD.Prelude
import AFTD.Kb.Tcs.IsTemporalWalk
import AFTD.Kb.Tcs.IsSpanningPathGraph

/-!
# temporal_path_many_targets_one_frame_trap

Topic: graphs   Node: 28a0feda5630

Provenance: original. Related work: OP-80, arXiv:2610.06228 Sec. 7. A relocation construction developed in the deep session to test an auxiliary prescribed-start constant-fraction coverage principle. The construction is a diagnostic for that proof route and is not an asymptotic lower-bound advance.

For every k ≥ 2 there is a temporal graph on N = k² + k vertices, all of whose snapshots are spanning paths, together with k designated targets and a start vertex, such that every walk from that start visits at most one target by time N − 1. This is an obstruction to a prescribed-start one-frame coverage principle considered while working on OP-80; the asymptotic exploration bound remains open.
-/

namespace TemporalPathTargetTrap

private abbrev vertex (k : ℕ) := (Fin k × Fin k) ⊕ Fin k

private def coordinate {k : ℕ} (t : ℕ) : vertex k → ℕ
  | Sum.inl (j, r) =>
      if r.val = 0 ∧ k * k + j.val ≤ t then k * k + j.val else r.val + k * j.val
  | Sum.inr j => if k * k + j.val ≤ t then k * j.val else k * k + j.val

private theorem coordinate_step_bound {k : ℕ} (hk : 0 < k) (t : ℕ) (v : vertex k) :
    coordinate (t + 1) v ≤ max (coordinate t v) (t + 1) := by
  rcases v with ⟨j, r⟩ | j
  · by_cases hr : r.val = 0
    · simp only [coordinate, hr, true_and, Nat.zero_add]
      by_cases h0 : k * k + j.val ≤ t
      · have h1 : k * k + j.val ≤ t + 1 := by omega
        simp [h0, h1]
      · by_cases h1 : k * k + j.val ≤ t + 1
        · simpa [h0, h1] using
            le_trans h1 (Nat.le_max_right (k * j.val) (t + 1))
        · simp [h0, h1]
    · simp [coordinate, hr]
  · have hj : k * j.val < k * k := Nat.mul_lt_mul_of_pos_left j.isLt hk
    by_cases h0 : k * k + j.val ≤ t
    · have h1 : k * k + j.val ≤ t + 1 := by omega
      simp [coordinate, h0, h1]
    · by_cases h1 : k * k + j.val ≤ t + 1
      · simp only [coordinate, h0, h1, if_true, if_false]
        exact le_trans (by omega) (Nat.le_max_right _ _)
      · simp [coordinate, h0, h1]

private theorem coordinate_step_fixed {k : ℕ} (hk : 0 < k) (q : Fin k)
    (t : ℕ) (ht : k * k + q.val ≤ t) (v : vertex k)
    (hv : coordinate t v < k * (q.val + 1)) :
    coordinate (t + 1) v = coordinate t v := by
  have hq : k * (q.val + 1) ≤ k * k :=
    Nat.mul_le_mul_left k (Nat.succ_le_of_lt q.isLt)
  rcases v with ⟨j, r⟩ | j
  · by_cases hr : r.val = 0
    · simp only [coordinate, hr, true_and, Nat.zero_add] at hv ⊢
      by_cases h0 : k * k + j.val ≤ t
      · have h1 : k * k + j.val ≤ t + 1 := by omega
        simp [h0, h1]
      · by_cases h1 : k * k + j.val ≤ t + 1
        · have hj : q.val + 1 ≤ j.val := by omega
          have hmul := Nat.mul_le_mul_left k hj
          simp only [h0, if_false] at hv
          omega
        · simp [h0, h1]
    · simp [coordinate, hr]
  · by_cases h0 : k * k + j.val ≤ t
    · have h1 : k * k + j.val ≤ t + 1 := by omega
      simp [coordinate, h0, h1]
    · simp only [coordinate, h0, if_false] at hv
      omega

private def coordinate_walk {k : ℕ} (v : ℕ → vertex k) : Prop :=
  ∀ t, v (t + 1) = v t ∨
    coordinate t (v t) + 1 = coordinate t (v (t + 1)) ∨
    coordinate t (v (t + 1)) + 1 = coordinate t (v t)

private theorem coordinate_walk_bounds {k : ℕ} (v : ℕ → vertex k)
    (hv : coordinate_walk v) (t : ℕ) :
    coordinate t (v (t + 1)) ≤ coordinate t (v t) + 1 ∧
      coordinate t (v t) ≤ coordinate t (v (t + 1)) + 1 := by
  rcases hv t with he | he | he
  · simp [he]
  · omega
  · omega

private theorem coordinate_walk_position {k : ℕ} (hk : 0 < k)
    (v : ℕ → vertex k) (hv : coordinate_walk v)
    (hv0 : coordinate 0 (v 0) = 0) :
    ∀ t, coordinate t (v t) ≤ t := by
  intro t
  induction t with
  | zero => omega
  | succ t ih =>
    have hm := (coordinate_walk_bounds v hv t).1
    have hs := coordinate_step_bound hk t (v (t + 1))
    omega

private theorem coordinate_target_active {k : ℕ} (v : ℕ → vertex k)
    (hpos : ∀ t, coordinate t (v t) ≤ t) (a : ℕ) (q : Fin k)
    (ha : v a = Sum.inr q) : k * k + q.val ≤ a := by
  have hp := hpos a
  rw [ha] at hp
  by_cases h : k * k + q.val ≤ a
  · exact h
  · simp [coordinate, h] at hp

private theorem coordinate_after_target {k : ℕ} (hk : 0 < k)
    (v : ℕ → vertex k) (hv : coordinate_walk v)
    (hpos : ∀ t, coordinate t (v t) ≤ t) (a : ℕ) (q : Fin k)
    (ha : v a = Sum.inr q) :
    ∀ d, a + d < k * k + k →
      coordinate (a + d) (v (a + d)) ≤ k * q.val + d ∧
      k * q.val ≤ coordinate (a + d) (v (a + d)) + d := by
  have hactive := coordinate_target_active v hpos a q ha
  intro d
  induction d with
  | zero => simp [ha, coordinate, hactive]
  | succ d ih =>
    intro hd
    have hi := ih (by omega)
    have hm := coordinate_walk_bounds v hv (a + d)
    have hdlt : d + 1 < k := by omega
    have hp : coordinate (a + d) (v (a + d + 1)) < k * (q.val + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hfixed := coordinate_step_fixed hk q (a + d) (by omega)
      (v (a + d + 1)) hp
    have he : a + (d + 1) = a + d + 1 := by omega
    rw [he, hfixed]
    omega

private theorem coordinate_two_targets_equal {k : ℕ} (hk : 0 < k)
    (v : ℕ → vertex k) (hv : coordinate_walk v)
    (hpos : ∀ t, coordinate t (v t) ≤ t)
    (a b : ℕ) (hab : a ≤ b) (hb : b < k * k + k)
    (q r : Fin k) (ha : v a = Sum.inr q) (hbr : v b = Sum.inr r) : q = r := by
  have he : a + (b - a) = b := by omega
  have hh := coordinate_after_target hk v hv hpos a q ha (b - a) (by omega)
  rw [he, hbr] at hh
  have hractive := coordinate_target_active v hpos b r hbr
  simp only [coordinate, hractive, if_true] at hh
  have hd : b - a < k := by
    have := coordinate_target_active v hpos a q ha
    omega
  apply Fin.ext
  rcases lt_trichotomy q.val r.val with h | h | h
  · have hm : k * (q.val + 1) ≤ k * r.val := Nat.mul_le_mul_left k (by omega)
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega
  · exact h
  · have hm : k * (r.val + 1) ≤ k * q.val := Nat.mul_le_mul_left k (by omega)
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega

private def index_equiv (k : ℕ) : vertex k ≃ Fin (k * k + k) :=
  (Equiv.sumCongr (finProdFinEquiv : Fin k × Fin k ≃ Fin (k * k))
    (Equiv.refl (Fin k))).trans finSumFinEquiv

@[simp] private theorem index_inl {k : ℕ} (j r : Fin k) :
    ((index_equiv k) (Sum.inl (j, r))).val = r.val + k * j.val := rfl

@[simp] private theorem index_inr {k : ℕ} (j : Fin k) :
    ((index_equiv k) (Sum.inr j)).val = k * k + j.val := rfl

private def swap_at {k : ℕ} (hk : 0 < k) (t : ℕ) : vertex k → vertex k
  | Sum.inl (j, r) =>
      if r.val = 0 ∧ k * k + j.val ≤ t then Sum.inr j else Sum.inl (j, r)
  | Sum.inr j =>
      if k * k + j.val ≤ t then Sum.inl (j, ⟨0, hk⟩) else Sum.inr j

private theorem swap_at_involutive {k : ℕ} (hk : 0 < k) (t : ℕ) :
    Function.Involutive (swap_at hk t) := by
  intro v
  rcases v with ⟨j, r⟩ | j
  · by_cases hr : r.val = 0
    · have he : r = (⟨0, hk⟩ : Fin k) := Fin.ext hr
      subst r
      by_cases h : k * k + j.val ≤ t <;> simp [swap_at, h]
    · simp [swap_at, hr]
  · by_cases h : k * k + j.val ≤ t <;> simp [swap_at, h]

private def swap_equiv {k : ℕ} (hk : 0 < k) (t : ℕ) : vertex k ≃ vertex k :=
  ⟨swap_at hk t, swap_at hk t, swap_at_involutive hk t, swap_at_involutive hk t⟩

private def rank_equiv {k : ℕ} (hk : 0 < k) (t : ℕ) : vertex k ≃ Fin (k * k + k) :=
  (swap_equiv hk t).trans (index_equiv k)

@[simp] private theorem rank_coordinate {k : ℕ} (hk : 0 < k) (t : ℕ) (v : vertex k) :
    (rank_equiv hk t v).val = coordinate t v := by
  change ((index_equiv k) (swap_at hk t v)).val = coordinate t v
  rcases v with ⟨j, r⟩ | j
  · by_cases h : r.val = 0 ∧ k * k + j.val ≤ t <;>
      simp [swap_at, coordinate, h]
  · by_cases h : k * k + j.val ≤ t <;> simp [swap_at, coordinate, h]

private def order_fin {k : ℕ} (hk : 0 < k) (t : ℕ) : Equiv.Perm (Fin (k * k + k)) :=
  (index_equiv k).symm.trans (rank_equiv hk t)

private def graph {k : ℕ} (hk : 0 < k) (t : ℕ) : SimpleGraph (Fin (k * k + k)) :=
  (SimpleGraph.pathGraph (k * k + k)).comap (order_fin hk t)

private theorem graph_path {k : ℕ} (hk : 0 < k) (t : ℕ) :
    is_spanning_path_graph (graph hk t) :=
  ⟨order_fin hk t, fun _ _ => SimpleGraph.pathGraph_adj⟩

private theorem lifted_walk {k : ℕ} (hk : 0 < k)
    (w : ℕ → Fin (k * k + k)) (hw : is_temporal_walk (graph hk) w) :
    coordinate_walk (fun t => (index_equiv k).symm (w t)) := by
  intro t
  rcases hw t with he | he
  · left
    exact congrArg (index_equiv k).symm he
  · right
    simpa only [graph, SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj,
      order_fin, Equiv.trans_apply, rank_coordinate] using he

end TemporalPathTargetTrap

theorem temporal_path_many_targets_one_frame_trap (k : ℕ) (hk : 2 ≤ k) :
    ∃ (G : ℕ → SimpleGraph (Fin (k * k + k)))
      (U : Finset (Fin (k * k + k))) (s : Fin (k * k + k)),
      U.card = k ∧ (∀ t, is_spanning_path_graph (G t)) ∧
      ∀ w : ℕ → Fin (k * k + k), w 0 = s → is_temporal_walk G w →
        ∀ a < k * k + k, ∀ b < k * k + k,
          w a ∈ U → w b ∈ U → w a = w b := by
  classical
  have hkpos : 0 < k := by omega
  let z : Fin k := ⟨0, hkpos⟩
  let f : Fin k → Fin (k * k + k) := fun j =>
    (TemporalPathTargetTrap.index_equiv k) (Sum.inr j)
  let U : Finset (Fin (k * k + k)) := Finset.univ.image f
  let s := (TemporalPathTargetTrap.index_equiv k) (Sum.inl (z, z))
  have hinj : Function.Injective f := by
    intro i j hij
    exact Sum.inr.inj ((TemporalPathTargetTrap.index_equiv k).injective hij)
  refine ⟨TemporalPathTargetTrap.graph hkpos, U, s, ?_,
    TemporalPathTargetTrap.graph_path hkpos, ?_⟩
  · simp [U, Finset.card_image_of_injective _ hinj]
  · intro w hw0 hw
    let v : ℕ → TemporalPathTargetTrap.vertex k := fun t =>
      (TemporalPathTargetTrap.index_equiv k).symm (w t)
    have hv : TemporalPathTargetTrap.coordinate_walk v := TemporalPathTargetTrap.lifted_walk hkpos w hw
    have hv0 : TemporalPathTargetTrap.coordinate 0 (v 0) = 0 := by
      have hsq : 0 < k * k := Nat.mul_pos hkpos hkpos
      simp [v, hw0, s, z, TemporalPathTargetTrap.coordinate, show ¬ k * k ≤ 0 by omega]
    have hpos := TemporalPathTargetTrap.coordinate_walk_position hkpos v hv hv0
    intro a ha b hb haU hbU
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp haU
    obtain ⟨r, -, hr⟩ := Finset.mem_image.mp hbU
    have hqa : v a = Sum.inr q := by
      dsimp [v]
      rw [← hq]
      exact (TemporalPathTargetTrap.index_equiv k).symm_apply_apply _
    have hrb : v b = Sum.inr r := by
      dsimp [v]
      rw [← hr]
      exact (TemporalPathTargetTrap.index_equiv k).symm_apply_apply _
    have hqr : q = r := by
      rcases le_total a b with hab | hba
      · exact TemporalPathTargetTrap.coordinate_two_targets_equal hkpos v hv hpos a b hab hb q r hqa hrb
      · exact (TemporalPathTargetTrap.coordinate_two_targets_equal hkpos v hv hpos b a hba ha r q hrb hqa).symm
    exact hq.symm.trans ((congrArg f hqr).trans hr)
