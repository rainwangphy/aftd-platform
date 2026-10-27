import AFTD.Prelude
import AFTD.Kb.Tcs.HasDegreeLe
import AFTD.Kb.Tcs.BentSumCounterexampleFunc

/-!
# bent_sum_counterexample_has_degree_le

Topic: cryptography   Node: d96beb590a21

Provenance: helper lemma. step towards bent_sum_counterexample_not_sum_of_two_bent

For any m ≥ 4, the Boolean function bent_sum_counterexample_func m hm has algebraic degree at most m.
-/

private lemma bent_sum_counterexample_has_degree_le_prod_insert_pair (m : ℕ) (x : Fin (2 * m) → ZMod 2)
    (u v : Fin (2 * m)) (huv : u ≠ v) (hu : m - 2 ≤ u.val) (hv : m - 2 ≤ v.val) :
    let S0 : Finset (Fin (2 * m)) := Finset.univ.image (fun (i : Fin (m - 2)) => ⟨i.val, by omega⟩)
    (∏ i ∈ insert u (insert v S0), x i) =
      (∏ i : Fin (m - 2), x ⟨i.val, by omega⟩) * (x u * x v) := by
  intro S0
  have hv_not : v ∉ S0 := by
    intro h
    simp only [S0, Finset.mem_image, Finset.mem_univ, true_and] at h
    rcases h with ⟨i, hi⟩
    have hi_val : (i : ℕ) = v.val := congrArg Fin.val hi
    have := i.isLt; omega
  have hu_not : u ∉ insert v S0 := by
    simp only [Finset.mem_insert]
    rintro (h | h)
    · exact huv h
    · simp only [S0, Finset.mem_image, Finset.mem_univ, true_and] at h
      rcases h with ⟨i, hi⟩
      have hi_val : (i : ℕ) = u.val := congrArg Fin.val hi
      have := i.isLt; omega
  rw [Finset.prod_insert hu_not, Finset.prod_insert hv_not]
  have hS0 : (∏ i ∈ S0, x i) = ∏ i : Fin (m - 2), x ⟨i.val, by omega⟩ := by
    dsimp [S0]
    rw [Finset.prod_image]
    intro a _ b _ h
    exact Fin.ext (by simpa using congrArg Fin.val h)
  rw [hS0]
  ring

/-- The counterexample Boolean function f_n on (Fin (2*m) → ZMod 2) has algebraic degree at most m. -/
theorem bent_sum_counterexample_has_degree_le (m : ℕ) (hm : 4 ≤ m) :
    has_degree_le (bent_sum_counterexample_func m hm) m := by
  unfold has_degree_le
  let S0 : Finset (Fin (2 * m)) := Finset.univ.image (fun (i : Fin (m - 2)) => ⟨i.val, by omega⟩)
  let a : Fin (2 * m) := ⟨m - 2, by omega⟩
  let b : Fin (2 * m) := ⟨m - 1, by omega⟩
  let c1 : Fin (2 * m) := ⟨m, by omega⟩
  let d1 : Fin (2 * m) := ⟨m + 1, by omega⟩
  let e : Fin (2 * m) := ⟨m + 2, by omega⟩
  let f1 : Fin (2 * m) := ⟨m + 3, by omega⟩
  let S1 := insert a (insert b S0)
  let S2 := insert c1 (insert d1 S0)
  let S3 := insert e (insert f1 S0)
  use {S1, S2, S3}
  have hS0_card : S0.card ≤ m - 2 := by
    dsimp [S0]
    refine le_trans Finset.card_image_le ?_
    simp
  have hS1_card : S1.card ≤ m := by
    dsimp [S1]
    refine le_trans (Finset.card_insert_le a _) ?_
    refine le_trans (Nat.add_le_add_right (Finset.card_insert_le b _) 1) ?_
    omega
  have hS2_card : S2.card ≤ m := by
    dsimp [S2]
    refine le_trans (Finset.card_insert_le c1 _) ?_
    refine le_trans (Nat.add_le_add_right (Finset.card_insert_le d1 _) 1) ?_
    omega
  have hS3_card : S3.card ≤ m := by
    dsimp [S3]
    refine le_trans (Finset.card_insert_le e _) ?_
    refine le_trans (Nat.add_le_add_right (Finset.card_insert_le f1 _) 1) ?_
    omega
  have hS0_mem : ∀ v ∈ S0, (v : Fin (2 * m)).val < m - 2 := by
    intro v hv
    simp only [S0, Finset.mem_image, Finset.mem_univ, true_and] at hv
    rcases hv with ⟨i, hi⟩
    have hi_val : (v : ℕ) = i.val := congrArg Fin.val hi.symm
    have := i.isLt; omega
  have ha1 : a ∈ S1 := Finset.mem_insert_self a _
  have ha2 : a ∉ S2 := by
    intro h
    simp only [S2, Finset.mem_insert] at h
    rcases h with h | h | h
    · apply_fun Fin.val at h; dsimp [a, c1] at h; omega
    · apply_fun Fin.val at h; dsimp [a, d1] at h; omega
    · have := hS0_mem a h; dsimp [a] at this; omega
  have ha3 : a ∉ S3 := by
    intro h
    simp only [S3, Finset.mem_insert] at h
    rcases h with h | h | h
    · apply_fun Fin.val at h; dsimp [a, e] at h; omega
    · apply_fun Fin.val at h; dsimp [a, f1] at h; omega
    · have := hS0_mem a h; dsimp [a] at this; omega
  have hc2 : c1 ∈ S2 := Finset.mem_insert_self c1 _
  have hc3 : c1 ∉ S3 := by
    intro h
    simp only [S3, Finset.mem_insert] at h
    rcases h with h | h | h
    · apply_fun Fin.val at h; dsimp [c1, e] at h; omega
    · apply_fun Fin.val at h; dsimp [c1, f1] at h; omega
    · have := hS0_mem c1 h; dsimp [c1] at this; omega
  have h12 : S1 ≠ S2 := by intro h; apply ha2; rw [← h]; exact ha1
  have h13 : S1 ≠ S3 := by intro h; apply ha3; rw [← h]; exact ha1
  have h23 : S2 ≠ S3 := by intro h; apply hc3; rw [← h]; exact hc2
  constructor
  · intro S hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl
    · exact hS1_card
    · exact hS2_card
    · exact hS3_card
  · intro x
    have hs12 : S1 ∉ ({S2, S3} : Finset (Finset (Fin (2 * m)))) := by
      simp [h12, h13]
    have hs23 : S2 ∉ ({S3} : Finset (Finset (Fin (2 * m)))) := by
      simp [h23]
    rw [Finset.sum_insert hs12, Finset.sum_insert hs23, Finset.sum_singleton]
    have hab : a ≠ b := by
      intro h; apply_fun Fin.val at h; dsimp [a, b] at h; omega
    have hcd : c1 ≠ d1 := by
      intro h; apply_fun Fin.val at h; dsimp [c1, d1] at h; omega
    have hef : e ≠ f1 := by
      intro h; apply_fun Fin.val at h; dsimp [e, f1] at h; omega
    have ha_val : m - 2 ≤ a.val := by dsimp [a]; omega
    have hb_val : m - 2 ≤ b.val := by dsimp [b]; omega
    have hc_val : m - 2 ≤ c1.val := by dsimp [c1]; omega
    have hd_val : m - 2 ≤ d1.val := by dsimp [d1]; omega
    have he_val : m - 2 ≤ e.val := by dsimp [e]; omega
    have hf_val : m - 2 ≤ f1.val := by dsimp [f1]; omega
    have hp1 := bent_sum_counterexample_has_degree_le_prod_insert_pair m x a b hab ha_val hb_val
    have hp2 := bent_sum_counterexample_has_degree_le_prod_insert_pair m x c1 d1 hcd hc_val hd_val
    have hp3 := bent_sum_counterexample_has_degree_le_prod_insert_pair m x e f1 hef he_val hf_val
    dsimp [bent_sum_counterexample_func]
    rw [hp1, hp2, hp3]
    ring
