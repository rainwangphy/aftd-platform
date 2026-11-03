import AFTD.Prelude
import AFTD.Kb.Tcs.Circulant13

/-!
# circulant_1_3_three_colorable

Topic: graphs   Node: fe6fc8b5683a

Provenance: formalization of a published result. Source: arXiv:2610.41820 Section 2.3

For every integer n ≥ 8, the circulant graph C_n(1,3) has a proper vertex 3-colouring, so N_3(C_n(1,3)) > 0.
-/

def circulant_1_3_three_colorable_coloring_of_steps (n : ℕ) [NeZero n] (f : ZMod n → Fin 3)
    (h1 : ∀ u : ZMod n, f u ≠ f (u + 1))
    (h3 : ∀ u : ZMod n, f u ≠ f (u + 3)) :
    (circulant_1_3 n).Coloring (Fin 3) := by
  refine ⟨f, ?_⟩
  intro u v huv
  simp only [circulant_1_3, SimpleGraph.circulantGraph_adj, Set.mem_insert_iff, Set.mem_singleton_iff] at huv
  rcases huv with ⟨hne, hstep⟩
  rcases hstep with (h | h) <;> rcases h with (h | h | h | h)
  · have : u = v + 1 := by linear_combination h
    rw [this]; exact (h1 v).symm
  · have : v = u + 1 := by linear_combination -h
    rw [this]; exact h1 u
  · have : u = v + 3 := by linear_combination h
    rw [this]; exact (h3 v).symm
  · have : v = u + 3 := by linear_combination -h
    rw [this]; exact h3 u
  · have : v = u + 1 := by linear_combination h
    rw [this]; exact h1 u
  · have : u = v + 1 := by linear_combination -h
    rw [this]; exact (h1 v).symm
  · have : v = u + 3 := by linear_combination h
    rw [this]; exact h3 u
  · have : u = v + 3 := by linear_combination -h
    rw [this]; exact (h3 v).symm

theorem circulant_1_3_three_colorable_even (n : ℕ) [NeZero n] (h2 : 2 ∣ n) :
    ∃ f : ZMod n → Fin 3, (∀ u, f u ≠ f (u + 1)) ∧ (∀ u, f u ≠ f (u + 3)) := by
  let phi : ZMod n →+* ZMod 2 := ZMod.castHom h2 (ZMod 2)
  let f : ZMod n → Fin 3 := fun u => (phi u).castLE (by decide)
  have hinj : Function.Injective (Fin.castLE (by decide : 2 ≤ 3)) := Fin.castLE_injective (by decide)
  refine ⟨f, ?_, ?_⟩
  · intro u hu
    apply hinj at hu
    have h1 : phi (u + 1) = phi u + 1 := by simp
    have hne : phi (u + 1) ≠ phi u := by
      rw [h1]
      intro heq
      have : (1 : ZMod 2) = 0 := by
        calc (1 : ZMod 2) = (phi u + 1) - phi u := by ring
        _ = phi u - phi u := by rw [heq]
        _ = 0 := by ring
      revert this; decide
    exact hne hu.symm
  · intro u hu
    apply hinj at hu
    have h3 : phi (u + 3) = phi u + 1 := by
      rw [map_add, map_ofNat]
      rw [show (3 : ZMod 2) = 1 by decide]
    have hne : phi (u + 3) ≠ phi u := by
      rw [h3]
      intro heq
      have : (1 : ZMod 2) = 0 := by
        calc (1 : ZMod 2) = (phi u + 1) - phi u := by ring
        _ = phi u - phi u := by rw [heq]
        _ = 0 := by ring
      revert this; decide
    exact hne hu.symm

def circulant_1_3_three_colorable_c_val (n i : ℕ) : ℕ :=
  if i = n - 5 then 2
  else if i = n - 4 then 1
  else if i = n - 3 then 2
  else if i = n - 2 then 0
  else if i = n - 1 then 2
  else i % 2

lemma circulant_1_3_three_colorable_c_val_lt (n i : ℕ) : circulant_1_3_three_colorable_c_val n i < 3 := by
  dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega

lemma circulant_1_3_three_colorable_c_val_step1 (n : ℕ) (hn : 9 ≤ n) (hodd : n % 2 = 1) (i : ℕ) (hi : i < n) :
    circulant_1_3_three_colorable_c_val n i ≠ circulant_1_3_three_colorable_c_val n ((i + 1) % n) := by
  have h0 : circulant_1_3_three_colorable_c_val n 0 = 0 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  have hn6 : circulant_1_3_three_colorable_c_val n (n - 6) = 1 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  have hn5 : circulant_1_3_three_colorable_c_val n (n - 5) = 2 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  have hn4 : circulant_1_3_three_colorable_c_val n (n - 4) = 1 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  have hn3 : circulant_1_3_three_colorable_c_val n (n - 3) = 2 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  have hn2 : circulant_1_3_three_colorable_c_val n (n - 2) = 0 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  have hn1 : circulant_1_3_three_colorable_c_val n (n - 1) = 2 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  rcases lt_or_ge i (n - 6) with hlt | hge
  · have hi1 : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hi1]
    have hci : circulant_1_3_three_colorable_c_val n i = i % 2 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
    have hci1 : circulant_1_3_three_colorable_c_val n (i + 1) = (i + 1) % 2 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
    rw [hci, hci1]; omega
  · have : i = n - 6 ∨ i = n - 5 ∨ i = n - 4 ∨ i = n - 3 ∨ i = n - 2 ∨ i = n - 1 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    · have : (n - 6 + 1) % n = n - 5 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [this, hn6, hn5]; decide
    · have : (n - 5 + 1) % n = n - 4 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [this, hn5, hn4]; decide
    · have : (n - 4 + 1) % n = n - 3 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [this, hn4, hn3]; decide
    · have : (n - 3 + 1) % n = n - 2 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [this, hn3, hn2]; decide
    · have : (n - 2 + 1) % n = n - 1 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [this, hn2, hn1]; decide
    · have : (n - 1 + 1) % n = 0 := by
        have : n - 1 + 1 = n := by omega
        rw [this, Nat.mod_self]
      rw [this, hn1, h0]; decide

lemma circulant_1_3_three_colorable_c_val_step3 (n : ℕ) (hn : 9 ≤ n) (hodd : n % 2 = 1) (i : ℕ) (hi : i < n) :
    circulant_1_3_three_colorable_c_val n i ≠ circulant_1_3_three_colorable_c_val n ((i + 3) % n) := by
  have h0 : circulant_1_3_three_colorable_c_val n 0 = 0 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  have h1 : circulant_1_3_three_colorable_c_val n 1 = 1 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  have h2 : circulant_1_3_three_colorable_c_val n 2 = 0 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  have hn8 : circulant_1_3_three_colorable_c_val n (n - 8) = 1 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  have hn7 : circulant_1_3_three_colorable_c_val n (n - 7) = 0 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  have hn6 : circulant_1_3_three_colorable_c_val n (n - 6) = 1 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  have hn5 : circulant_1_3_three_colorable_c_val n (n - 5) = 2 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  have hn4 : circulant_1_3_three_colorable_c_val n (n - 4) = 1 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  have hn3 : circulant_1_3_three_colorable_c_val n (n - 3) = 2 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  have hn2 : circulant_1_3_three_colorable_c_val n (n - 2) = 0 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  have hn1 : circulant_1_3_three_colorable_c_val n (n - 1) = 2 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
  rcases lt_or_ge i (n - 8) with hlt | hge
  · have hi3 : (i + 3) % n = i + 3 := Nat.mod_eq_of_lt (by omega)
    rw [hi3]
    have hci : circulant_1_3_three_colorable_c_val n i = i % 2 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
    have hci3 : circulant_1_3_three_colorable_c_val n (i + 3) = (i + 3) % 2 := by dsimp [circulant_1_3_three_colorable_c_val]; split_ifs <;> omega
    rw [hci, hci3]; omega
  · have : i = n - 8 ∨ i = n - 7 ∨ i = n - 6 ∨ i = n - 5 ∨ i = n - 4 ∨ i = n - 3 ∨ i = n - 2 ∨ i = n - 1 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : (n - 8 + 3) % n = n - 5 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [this, hn8, hn5]; decide
    · have : (n - 7 + 3) % n = n - 4 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [this, hn7, hn4]; decide
    · have : (n - 6 + 3) % n = n - 3 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [this, hn6, hn3]; decide
    · have : (n - 5 + 3) % n = n - 2 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [this, hn5, hn2]; decide
    · have : (n - 4 + 3) % n = n - 1 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [this, hn4, hn1]; decide
    · have : (n - 3 + 3) % n = 0 := by
        have : n - 3 + 3 = n := by omega
        rw [this, Nat.mod_self]
      rw [this, hn3, h0]; decide
    · have : (n - 2 + 3) % n = 1 := by
        have : n - 2 + 3 = n + 1 := by omega
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      rw [this, hn2, h1]; decide
    · have : (n - 1 + 3) % n = 2 := by
        have : n - 1 + 3 = n + 2 := by omega
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      rw [this, hn1, h2]; decide

def circulant_1_3_three_colorable_odd_fn (n : ℕ) (u : ZMod n) : Fin 3 :=
  ⟨circulant_1_3_three_colorable_c_val n u.val, circulant_1_3_three_colorable_c_val_lt n u.val⟩

lemma circulant_1_3_three_colorable_odd_step1 (n : ℕ) [NeZero n] (hn : 9 ≤ n) (hodd : n % 2 = 1) (u : ZMod n) :
    circulant_1_3_three_colorable_odd_fn n u ≠ circulant_1_3_three_colorable_odd_fn n (u + 1) := by
  intro h
  have heq : circulant_1_3_three_colorable_c_val n u.val = circulant_1_3_three_colorable_c_val n (u + 1).val := congrArg Fin.val h
  have hu1 : (u + 1).val = (u.val + 1) % n := by
    have := ZMod.val_add u 1
    have h1 : (1 : ZMod n).val = 1 := by
      rw [← Nat.cast_one, ZMod.val_cast_of_lt (by omega)]
    rw [h1] at this; exact this
  rw [hu1] at heq
  exact circulant_1_3_three_colorable_c_val_step1 n hn hodd u.val (ZMod.val_lt u) heq

lemma circulant_1_3_three_colorable_odd_step3 (n : ℕ) [NeZero n] (hn : 9 ≤ n) (hodd : n % 2 = 1) (u : ZMod n) :
    circulant_1_3_three_colorable_odd_fn n u ≠ circulant_1_3_three_colorable_odd_fn n (u + 3) := by
  intro h
  have heq : circulant_1_3_three_colorable_c_val n u.val = circulant_1_3_three_colorable_c_val n (u + 3).val := congrArg Fin.val h
  have hu3 : (u + 3).val = (u.val + 3) % n := by
    have := ZMod.val_add u 3
    have h3 : (3 : ZMod n).val = 3 := by
      rw [show (3 : ZMod n) = ((3 : ℕ) : ZMod n) by rfl, ZMod.val_cast_of_lt (by omega)]
    rw [h3] at this; exact this
  rw [hu3] at heq
  exact circulant_1_3_three_colorable_c_val_step3 n hn hodd u.val (ZMod.val_lt u) heq

/-- Existence of proper 3-colourings for C_n(1,3) for every n ≥ 8. -/
theorem circulant_1_3_three_colorable (n : ℕ) [NeZero n] (hn : 8 ≤ n) :
    0 < Fintype.card ((circulant_1_3 n).Coloring (Fin 3)) := by
  rw [Fintype.card_pos_iff]
  by_cases h2 : 2 ∣ n
  · rcases circulant_1_3_three_colorable_even n h2 with ⟨f, h1, h3⟩
    exact ⟨circulant_1_3_three_colorable_coloring_of_steps n f h1 h3⟩
  · have hodd : n % 2 = 1 := by omega
    have hn9 : 9 ≤ n := by omega
    exact ⟨circulant_1_3_three_colorable_coloring_of_steps n (circulant_1_3_three_colorable_odd_fn n)
      (circulant_1_3_three_colorable_odd_step1 n hn9 hodd) (circulant_1_3_three_colorable_odd_step3 n hn9 hodd)⟩
