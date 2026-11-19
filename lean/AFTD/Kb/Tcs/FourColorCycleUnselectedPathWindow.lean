import AFTD.Prelude

/-!
# four_color_cycle_unselected_path_window

Topic: graphs   Node: df1fba8f546d

Provenance: helper lemma. Cycle-local helper for OP-874; experiments 33384, 33386 and 33387 independently test an explicit word construction. The separate matching and port constraints are not included.

For a cyclic sequence of n at least five edge positions, with at least one selected position when n is odd, there is a proper four-coloring of the cycle such that every four consecutive unselected edges has all four colors among its six incident factor edges, counted cyclically.
-/

def four_color_cycle_unselected_path_window_feven (n : ℕ) : Fin n → Fin 4 := fun k => ⟨k.val % 4, Nat.mod_lt _ (by norm_num)⟩
def four_color_cycle_unselected_path_window_fodd (n : ℕ) : Fin n → Fin 4 :=
  fun k => if k.val = n - 1 then ⟨2, by norm_num⟩ else ⟨k.val % 4, Nat.mod_lt _ (by norm_num)⟩

lemma four_color_cycle_unselected_path_window_four_consec_mod (a : ℕ) (c : Fin 4) : ∃ k : ℕ, k < 4 ∧ (a + k) % 4 = c.val := by
  refine ⟨(c.val + 4 - a % 4) % 4, ?_, ?_⟩ <;> omega

lemma four_color_cycle_unselected_path_window_even_special (n : ℕ) (hn : 6 ≤ n) (c : Fin 4) (h4 : n % 4 = 0 ∨ n % 4 = 2) :
    ∃ k : ℕ, k < 6 ∧ ((n - 3 + k) % n) % 4 = c.val := by
  rcases h4 with h4 | h4
  · fin_cases c
    · refine ⟨3, by norm_num, ?_⟩
      have heq : n - 3 + 3 = n := by omega
      have key : ((n - 3 + 3) % n) % 4 = 0 := by rw [heq]; simp [Nat.mod_self]
      exact key
    · refine ⟨0, by norm_num, ?_⟩
      have hlt : n - 3 + 0 < n := by omega
      have key : ((n - 3 + 0) % n) % 4 = 1 := by rw [Nat.mod_eq_of_lt hlt]; omega
      exact key
    · refine ⟨1, by norm_num, ?_⟩
      have hlt : n - 3 + 1 < n := by omega
      have key : ((n - 3 + 1) % n) % 4 = 2 := by rw [Nat.mod_eq_of_lt hlt]; omega
      exact key
    · refine ⟨2, by norm_num, ?_⟩
      have hlt : n - 3 + 2 < n := by omega
      have key : ((n - 3 + 2) % n) % 4 = 3 := by rw [Nat.mod_eq_of_lt hlt]; omega
      exact key
  · fin_cases c
    · refine ⟨1, by norm_num, ?_⟩
      have hlt : n - 3 + 1 < n := by omega
      have key : ((n - 3 + 1) % n) % 4 = 0 := by rw [Nat.mod_eq_of_lt hlt]; omega
      exact key
    · refine ⟨2, by norm_num, ?_⟩
      have hlt : n - 3 + 2 < n := by omega
      have key : ((n - 3 + 2) % n) % 4 = 1 := by rw [Nat.mod_eq_of_lt hlt]; omega
      exact key
    · refine ⟨5, by norm_num, ?_⟩
      have heq : n - 3 + 5 = n + 2 := by omega
      have key : ((n - 3 + 5) % n) % 4 = 2 := by
        rw [heq]
        have hmod : (n + 2) % n = 2 := by
          rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hmod]
      exact key
    · refine ⟨0, by norm_num, ?_⟩
      have hlt : n - 3 + 0 < n := by omega
      have key : ((n - 3 + 0) % n) % 4 = 3 := by rw [Nat.mod_eq_of_lt hlt]; omega
      exact key

lemma four_color_cycle_unselected_path_window_even_window_aux (n : ℕ) (hn : 6 ≤ n) (he : n % 2 = 0) (a : ℕ) (ha : a < n) (c : Fin 4) :
    ∃ k : ℕ, k < 6 ∧ ((a + k) % n) % 4 = c.val := by
  by_cases h1 : a ≤ n - 4
  · obtain ⟨k, hk, h⟩ := four_color_cycle_unselected_path_window_four_consec_mod a c
    refine ⟨k, by omega, ?_⟩
    have hv : (a + k) % n = a + k := Nat.mod_eq_of_lt (by omega)
    rw [hv]; exact h
  · have h1' : n - 4 < a := not_le.mp h1
    by_cases h2 : n - 2 ≤ a
    · refine ⟨(n - a) + c.val, ?_, ?_⟩
      · have := c.isLt; omega
      · have hsum : a + ((n - a) + c.val) = n + c.val := by omega
        rw [hsum]
        have hmod : (n + c.val) % n = c.val := by
          rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
          exact Nat.mod_eq_of_lt (by have := c.isLt; omega)
        rw [hmod]
        exact Nat.mod_eq_of_lt (by have := c.isLt; omega)
    · have h2' : a < n - 2 := not_le.mp h2
      have hae : a = n - 3 := by omega
      rw [hae]
      exact four_color_cycle_unselected_path_window_even_special n hn c (by omega)

lemma four_color_cycle_unselected_path_window_even_adj (n : ℕ) [NeZero n] (hn : 5 ≤ n) (he : n % 2 = 0) :
    ∀ i : Fin n, four_color_cycle_unselected_path_window_feven n i ≠ four_color_cycle_unselected_path_window_feven n (i + 1) := by
  intro i h
  have hv : i.val % 4 = (i + 1).val % 4 := by
    have := congrArg Fin.val h; simpa [four_color_cycle_unselected_path_window_feven] using this
  have hone : (1 : Fin n).val = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have hj1 : (i + 1).val = (i.val + 1) % n := by rw [Fin.val_add, hone]
  rw [hj1] at hv
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · have heq : i.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    simp at hv; omega

lemma four_color_cycle_unselected_path_window_even_window (n : ℕ) [NeZero n] (hn : 6 ≤ n) (he : n % 2 = 0) (q : Fin n) (c : Fin 4) :
    ∃ j : Fin 6, four_color_cycle_unselected_path_window_feven n (q + Fin.ofNat n j.val) = c := by
  obtain ⟨k, hk, hkc⟩ := four_color_cycle_unselected_path_window_even_window_aux n hn he q.val q.isLt c
  refine ⟨⟨k, by omega⟩, ?_⟩
  have hvq : (q + Fin.ofNat n k).val = (q.val + k) % n := by
    rw [Fin.val_add]
    have hkv : (Fin.ofNat n k).val = k := by rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hkv]
  apply Fin.ext
  show (q + Fin.ofNat n k).val % 4 = c.val
  rw [hvq]; exact hkc

lemma four_color_cycle_unselected_path_window_sub_add_eq_zero (n : ℕ) [NeZero n] (i s x : Fin n) (h : (i - s) + x = 0) : i + x = s := by
  have h2 : (i - s) + x + s = s := by rw [h, zero_add]
  rwa [show (i - s) + x + s = i + x by abel] at h2

lemma four_color_cycle_unselected_path_window_p_bounds (n : ℕ) [NeZero n] (hn : 5 ≤ n) (p : Fin n)
    (h0 : p + Fin.ofNat n 0 ≠ 0) (h1 : p + Fin.ofNat n 1 ≠ 0)
    (h2 : p + Fin.ofNat n 2 ≠ 0) (h3 : p + Fin.ofNat n 3 ≠ 0) :
    1 ≤ p.val ∧ p.val ≤ n - 4 := by
  have hk : ∀ k : ℕ, k ≤ 3 → (p + Fin.ofNat n k).val = (p.val + k) % n := by
    intro k hk
    have hkv : (Fin.ofNat n k).val = k := by rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [Fin.val_add, hkv]
  have h0v : (p.val + 0) % n ≠ 0 := by
    rw [← hk 0 (by norm_num)]; intro hh; apply h0; apply Fin.ext; rw [hh, Fin.val_zero]
  have h1v : (p.val + 1) % n ≠ 0 := by
    rw [← hk 1 (by norm_num)]; intro hh; apply h1; apply Fin.ext; rw [hh, Fin.val_zero]
  have h2v : (p.val + 2) % n ≠ 0 := by
    rw [← hk 2 (by norm_num)]; intro hh; apply h2; apply Fin.ext; rw [hh, Fin.val_zero]
  have h3v : (p.val + 3) % n ≠ 0 := by
    rw [← hk 3 (by norm_num)]; intro hh; apply h3; apply Fin.ext; rw [hh, Fin.val_zero]
  have hp0 : p.val ≠ 0 := by intro he; apply h0v; rw [he]; simp
  have hp1 : p.val + 1 ≠ n := by intro he; apply h1v; rw [he]; exact Nat.mod_self n
  have hp2 : p.val + 2 ≠ n := by intro he; apply h2v; rw [he]; exact Nat.mod_self n
  have hp3 : p.val + 3 ≠ n := by intro he; apply h3v; rw [he]; exact Nat.mod_self n
  have := p.isLt; omega

lemma four_color_cycle_unselected_path_window_odd_val (n : ℕ) (j : Fin n) :
    (four_color_cycle_unselected_path_window_fodd n j).val = if j.val = n - 1 then 2 else j.val % 4 := by
  unfold four_color_cycle_unselected_path_window_fodd; by_cases h : j.val = n - 1 <;> simp [h]

lemma four_color_cycle_unselected_path_window_odd_adj (n : ℕ) [NeZero n] (hn : 5 ≤ n) (hodd : n % 2 = 1) :
    ∀ j : Fin n, four_color_cycle_unselected_path_window_fodd n j ≠ four_color_cycle_unselected_path_window_fodd n (j + 1) := by
  intro j h
  have hv : (four_color_cycle_unselected_path_window_fodd n j).val = (four_color_cycle_unselected_path_window_fodd n (j + 1)).val := by rw [h]
  rw [four_color_cycle_unselected_path_window_odd_val, four_color_cycle_unselected_path_window_odd_val] at hv
  have hone : (1 : Fin n).val = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have hj1 : (j + 1).val = (j.val + 1) % n := by rw [Fin.val_add, hone]
  rw [hj1] at hv
  have h4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
  have hzero : (n - 1 + 1) % n = 0 := by rw [show n-1+1 = n by omega, Nat.mod_self]
  rcases h4 with h4 | h4
  · by_cases hj : j.val = n - 1
    · rw [hj] at hv; rw [hzero] at hv
      rw [if_pos rfl, if_neg (by omega : ¬ ((0:ℕ) = n - 1))] at hv; simp at hv
    · by_cases hj2 : j.val = n - 2
      · rw [hj2] at hv
        rw [show (n - 2 + 1) % n = n - 1 by rw [Nat.mod_eq_of_lt (by omega)]; omega] at hv
        rw [if_neg (by omega : ¬ (n-2 = n-1)), if_pos rfl] at hv; omega
      · have hlt : j.val + 1 < n := by omega
        rw [Nat.mod_eq_of_lt hlt] at hv
        rw [if_neg hj, if_neg (by omega : ¬ (j.val + 1 = n - 1))] at hv; omega
  · by_cases hj : j.val = n - 1
    · rw [hj] at hv; rw [hzero] at hv
      rw [if_pos rfl, if_neg (by omega : ¬ ((0:ℕ) = n - 1))] at hv; simp at hv
    · by_cases hj2 : j.val = n - 2
      · rw [hj2] at hv
        rw [show (n - 2 + 1) % n = n - 1 by rw [Nat.mod_eq_of_lt (by omega)]; omega] at hv
        rw [if_neg (by omega : ¬ (n-2 = n-1)), if_pos rfl] at hv; omega
      · have hlt : j.val + 1 < n := by omega
        rw [Nat.mod_eq_of_lt hlt] at hv
        rw [if_neg hj, if_neg (by omega : ¬ (j.val + 1 = n - 1))] at hv; omega

lemma four_color_cycle_unselected_path_window_odd_window (n : ℕ) [NeZero n] (hn : 5 ≤ n) (q : Fin n) (hq : q.val ≤ n - 5) (c : Fin 4) :
    ∃ j : Fin 6, four_color_cycle_unselected_path_window_fodd n (q + Fin.ofNat n j.val) = c := by
  obtain ⟨k, hk, hkc⟩ := four_color_cycle_unselected_path_window_four_consec_mod q.val c
  refine ⟨⟨k, by omega⟩, ?_⟩
  have hvq : (q + Fin.ofNat n k).val = q.val + k := by
    rw [Fin.val_add]
    have hkv : (Fin.ofNat n k).val = k := by rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hkv]; exact Nat.mod_eq_of_lt (by omega)
  apply Fin.ext
  rw [four_color_cycle_unselected_path_window_odd_val, hvq]
  rw [if_neg (by omega : ¬ (q.val + k = n - 1))]
  exact hkc

theorem four_color_cycle_unselected_path_window (n : ℕ) [NeZero n] (hn : 5 ≤ n) (S : Finset (Fin n)) (hodd : Odd n → S.Nonempty) : ∃ f : Fin n → Fin 4, (∀ i, f i ≠ f (i + 1)) ∧ ∀ i : Fin n, (∀ j : Fin 4, i + (Fin.ofNat n j.val) ∉ S) → ∀ c : Fin 4, ∃ j : Fin 6, f (i - 1 + (Fin.ofNat n j.val)) = c := by
  by_cases he : n % 2 = 0
  · refine ⟨four_color_cycle_unselected_path_window_feven n, four_color_cycle_unselected_path_window_even_adj n hn he, ?_⟩
    intro i _ c
    exact four_color_cycle_unselected_path_window_even_window n (by omega) he (i - 1) c
  · have hn2 : n % 2 = 1 := by have := Nat.mod_lt n (by norm_num : 0 < 2); omega
    obtain ⟨s, hs⟩ := hodd (Nat.odd_iff.mpr hn2)
    refine ⟨fun i => four_color_cycle_unselected_path_window_fodd n (i - s), ?_, ?_⟩
    · intro i
      show four_color_cycle_unselected_path_window_fodd n (i - s) ≠ four_color_cycle_unselected_path_window_fodd n (i + 1 - s)
      rw [show i + 1 - s = (i - s) + 1 by abel]
      exact four_color_cycle_unselected_path_window_odd_adj n hn hn2 (i - s)
    · intro i hS c
      have hmk : ∀ k : ℕ, k ≤ 3 → (i - s) + Fin.ofNat n k ≠ 0 := by
        intro k hk
        have hSk : i + Fin.ofNat n k ∉ S := by have := hS ⟨k, by omega⟩; simpa using this
        have hne : i + Fin.ofNat n k ≠ s := fun heq => hSk (heq ▸ hs)
        intro hh; exact hne (four_color_cycle_unselected_path_window_sub_add_eq_zero n i s (Fin.ofNat n k) hh)
      have hp := four_color_cycle_unselected_path_window_p_bounds n hn (i - s) (hmk 0 (by norm_num)) (hmk 1 (by norm_num)) (hmk 2 (by norm_num)) (hmk 3 (by norm_num))
      obtain ⟨hp1, hp2⟩ := hp
      have hpne : (i - s) ≠ 0 := by intro hh; rw [hh] at hp1; simp at hp1
      have hqval : ((i - s) - 1).val = (i - s).val - 1 := Fin.val_sub_one_of_ne_zero hpne
      have hq : ((i - s) - 1).val ≤ n - 5 := by rw [hqval]; omega
      obtain ⟨j, hj⟩ := four_color_cycle_unselected_path_window_odd_window n hn ((i - s) - 1) hq c
      refine ⟨j, ?_⟩
      show four_color_cycle_unselected_path_window_fodd n (i - 1 + Fin.ofNat n j.val - s) = c
      rw [show i - 1 + Fin.ofNat n j.val - s = ((i - s) - 1) + Fin.ofNat n j.val by abel]
      exact hj
