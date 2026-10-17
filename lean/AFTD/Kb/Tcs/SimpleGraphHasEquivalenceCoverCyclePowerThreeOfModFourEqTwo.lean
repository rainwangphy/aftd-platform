import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerThreeAdjIff

/-!
# simple_graph_has_equivalence_cover_cycle_power_three_of_mod_four_eq_two

Topic: combinatorics   Node: d0d5cfe3df93

Provenance: helper lemma. Upper bound for the k = 3 case of OP-205 (arXiv:2610.15635), generalizing the SAT cover of C_46^3 (experiment 738); pattern checked for n ≤ 402 (experiment 763).

For every n ≥ 10 with n ≡ 2 (mod 4), the cube C_n^3 of the n-cycle is covered by 4 equivalence subgraphs: on 0..n−1, layer 0 has the blocks {4j..4j+3} (1 ≤ j < (n−2)/4) and {n−2, n−1, 0, 1}, {2, 3}; layer 1 the pairs {i, i+3} for odd i; layers 2 and 3 the blocks {4j+2..4j+5} (j ≥ 1) with {0..3}, {4, 5} resp. {0, 1}, {2..5}.
-/

/-- The four labellings of the 4-cover of `C_n^3`, `n ≡ 2 (mod 4)`, on `0, ..., n - 1`. -/
def simple_graph_cycle_power_three_mod_four_two_label (n : ℕ) : Fin 4 → ℕ → ℕ
  | 0, x => if n - 2 ≤ x ∨ x < 2 then 0 else if x < 4 then 2 else 4 * (x / 4)
  | 1, x => if x % 2 = 1 then x else if 4 ≤ x then x - 3 else if x = 0 then n - 3 else n - 1
  | 2, x => if x < 4 then 0 else if x < 6 then 4 else 4 * ((x - 2) / 4) + 2
  | 3, x => if x < 2 then 0 else if x < 6 then 2 else 4 * ((x - 2) / 4) + 2

theorem simple_graph_cycle_power_three_mod_four_two_label_lt (n : ℕ) (hn : 10 ≤ n) (s : Fin 4) (x : ℕ) (hx : x < n) : simple_graph_cycle_power_three_mod_four_two_label n s x < n := by
  fin_cases s <;> simp only [simple_graph_cycle_power_three_mod_four_two_label] <;> split_ifs <;> omega

/-- Same label in a layer: distinct points are at cyclic distance at most 3. -/
theorem simple_graph_cycle_power_three_mod_four_two_label_valid (n : ℕ) (hn : 10 ≤ n) (h4 : n % 4 = 2) (s : Fin 4) (x y : ℕ) (hx : x < n)
    (hy : y < n) (_hxy : x ≠ y) (h : simple_graph_cycle_power_three_mod_four_two_label n s x = simple_graph_cycle_power_three_mod_four_two_label n s y) (du dv : ℕ)
    (hdu : du + y = x ∨ du + y = x + n) (hdv : dv + x = y ∨ dv + x = y + n) (hdu' : du < n)
    (hdv' : dv < n) : min du dv ≤ 3 := by
  fin_cases s <;> simp only [simple_graph_cycle_power_three_mod_four_two_label] at h <;> split_ifs at h <;> omega

theorem simple_graph_cycle_power_three_mod_four_two_label_cover_small (n : ℕ) (hn : 10 ≤ n) (h4 : n % 4 = 2) (x e y : ℕ) (hx : x < n)
    (he1 : 1 ≤ e) (he3 : e ≤ 3) (hy : y < n) (hxy : y = x + e ∨ y + n = x + e) (hr : x < 6) :
    ∃ s, simple_graph_cycle_power_three_mod_four_two_label n s x = simple_graph_cycle_power_three_mod_four_two_label n s y := by
  interval_cases x <;> interval_cases e
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨2, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨2, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨2, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨2, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨1, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨3, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨3, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨3, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨3, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨1, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨1, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩

theorem simple_graph_cycle_power_three_mod_four_two_label_cover_seam (n : ℕ) (hn : 10 ≤ n) (h4 : n % 4 = 2) (x e y : ℕ) (hx : x < n)
    (he1 : 1 ≤ e) (he3 : e ≤ 3) (hy : y < n) (hxy : y = x + e ∨ y + n = x + e) (hr : n - 6 ≤ x) :
    ∃ s, simple_graph_cycle_power_three_mod_four_two_label n s x = simple_graph_cycle_power_three_mod_four_two_label n s y := by
  obtain ⟨t, rfl⟩ : ∃ t, x = n - 6 + t := ⟨x - (n - 6), by omega⟩
  have ht : t < 6 := by omega
  interval_cases t <;> interval_cases e
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨1, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨2, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨2, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨2, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨2, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨1, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨1, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩

theorem simple_graph_cycle_power_three_mod_four_two_label_cover_inter (n : ℕ) (hn : 10 ≤ n) (h4 : n % 4 = 2) (x e y : ℕ) (hx : x < n)
    (he1 : 1 ≤ e) (he3 : e ≤ 3) (hy : y < n) (hxy : y = x + e ∨ y + n = x + e) (hr : 6 ≤ x ∧ x < n - 6) :
    ∃ s, simple_graph_cycle_power_three_mod_four_two_label n s x = simple_graph_cycle_power_three_mod_four_two_label n s y := by
  have hy' : y = x + e := by omega
  subst hy'
  rcases (by omega : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3) with hm | hm | hm | hm <;>
    interval_cases e
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨1, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨0, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨2, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨2, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨2, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨2, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩
  · exact ⟨1, by simp only [simple_graph_cycle_power_three_mod_four_two_label]; split_ifs <;> omega⟩

/-- Each pair at cyclic distance `e ∈ {1, 2, 3}` shares a label in some layer. -/
theorem simple_graph_cycle_power_three_mod_four_two_label_cover (n : ℕ) (hn : 10 ≤ n) (h4 : n % 4 = 2) (x e y : ℕ) (hx : x < n)
    (he1 : 1 ≤ e) (he3 : e ≤ 3) (hy : y < n) (hxy : y = x + e ∨ y + n = x + e) :
    ∃ s, simple_graph_cycle_power_three_mod_four_two_label n s x = simple_graph_cycle_power_three_mod_four_two_label n s y := by
  rcases (by omega : x < 6 ∨ n - 6 ≤ x ∨ (6 ≤ x ∧ x < n - 6)) with hr | hr | hr
  · exact simple_graph_cycle_power_three_mod_four_two_label_cover_small n hn h4 x e y hx he1 he3 hy hxy hr
  · exact simple_graph_cycle_power_three_mod_four_two_label_cover_seam n hn h4 x e y hx he1 he3 hy hxy hr
  · exact simple_graph_cycle_power_three_mod_four_two_label_cover_inter n hn h4 x e y hx he1 he3 hy hxy hr

theorem simple_graph_has_equivalence_cover_cycle_power_three_of_mod_four_eq_two (n : ℕ) (hn : 10 ≤ n) (h4 : n % 4 = 2) :
    simple_graph_has_equivalence_cover (simple_graph_cycle_power n 3) 4 := by
  have : NeZero n := ⟨by omega⟩
  have hsub : ∀ u v : ZMod n, (u - v).val + v.val = u.val ∨ (u - v).val + v.val = u.val + n := by
    intro u v
    have h1 := ZMod.val_add (u - v) v
    rw [sub_add_cancel] at h1
    have := ZMod.val_lt (u - v); have := ZMod.val_lt v
    rcases lt_or_ge ((u - v).val + v.val) n with h | h
    · left; rw [Nat.mod_eq_of_lt h] at h1; omega
    · right; rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)] at h1; omega
  have hinj : ∀ a b : ℕ, a < n → b < n → ((a : ZMod n) = (b : ZMod n)) → a = b := by
    intro a b ha hb h
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  have key : ∀ (w : ZMod n) (k : ℕ), 1 ≤ k → k ≤ 3 →
      ∃ s, simple_graph_cycle_power_three_mod_four_two_label n s w.val = simple_graph_cycle_power_three_mod_four_two_label n s (w + (k : ZMod n)).val := by
    intro w k h1 h3
    have hv := ZMod.val_add w (k : ZMod n)
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : k < n)] at hv
    have hw := ZMod.val_lt w
    refine simple_graph_cycle_power_three_mod_four_two_label_cover n hn h4 w.val k _ hw h1 h3 (ZMod.val_lt _) ?_
    rcases lt_or_ge (w.val + k) n with h | h
    · left; rw [hv, Nat.mod_eq_of_lt h]
    · right; rw [hv, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega
  refine ⟨fun s u => (simple_graph_cycle_power_three_mod_four_two_label n s u.val : ZMod n), fun s u v huv h => ?_, fun u v h => ?_⟩
  · have hx := ZMod.val_lt u; have hy := ZMod.val_lt v
    have h' := hinj _ _ (simple_graph_cycle_power_three_mod_four_two_label_lt n hn s _ hx) (simple_graph_cycle_power_three_mod_four_two_label_lt n hn s _ hy) h
    have hne : u.val ≠ v.val := fun e => huv (ZMod.val_injective n e)
    exact ⟨huv, simple_graph_cycle_power_three_mod_four_two_label_valid n hn h4 s u.val v.val hx hy hne h' (u - v).val (v - u).val
      (hsub u v) (hsub v u) (ZMod.val_lt _) (ZMod.val_lt _)⟩
  · obtain ⟨e, he0, he3, rfl⟩ := (simple_graph_cycle_power_three_adj_iff n hn u v).1 h
    have he := abs_le.1 he3
    rcases lt_or_gt_of_ne he0 with hneg | hpos
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, e = -(k : ℤ) := ⟨(-e).toNat, by omega⟩
      obtain ⟨s, hs⟩ := key (u + ((-(k : ℤ) : ℤ) : ZMod n)) k (by omega) (by omega)
      have hu : u + ((-(k : ℤ) : ℤ) : ZMod n) + (k : ZMod n) = u := by push_cast; ring
      rw [hu] at hs
      exact ⟨s, by dsimp only; rw [hs]⟩
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, e = (k : ℤ) := ⟨e.toNat, by omega⟩
      obtain ⟨s, hs⟩ := key u k (by omega) (by omega)
      exact ⟨s, by dsimp only; push_cast; rw [hs]⟩
