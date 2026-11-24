import AFTD.Prelude

/-!
# cycle_square_four_colorable_except_five

Topic: graphs   Node: 5bdb692a1c5e

Provenance: helper lemma. Square-coloring input to the cycle demand reduction for OP-874.

Every cycle with at least three vertices except a five-cycle has a four-coloring of its square.
-/

def cycle_square_four_colorable_except_five_color_val (a : ℕ) (k : ℕ) : ℕ :=
  if k < 3 * a then k % 3 else (k - 3 * a) % 4

lemma cycle_square_four_colorable_except_five_color_val_lt_four (a k : ℕ) :
    cycle_square_four_colorable_except_five_color_val a k < 4 := by
  dsimp [cycle_square_four_colorable_except_five_color_val]
  split_ifs <;> omega

lemma cycle_square_four_colorable_except_five_color_val_ne_add_one
    (a b n : ℕ) (hn : 3 * a + 4 * b = n) (k : ℕ) (hk : k < n) :
    cycle_square_four_colorable_except_five_color_val a k ≠
      cycle_square_four_colorable_except_five_color_val a ((k + 1) % n) := by
  dsimp [cycle_square_four_colorable_except_five_color_val]
  by_cases hk1 : k + 1 < n
  · have h1 : (k + 1) % n = k + 1 := Nat.mod_eq_of_lt hk1
    rw [h1]
    split_ifs <;> omega
  · have h1 : (k + 1) % n = 0 := by
      have : k + 1 = n := by omega
      rw [this, Nat.mod_self]
    rw [h1]
    split_ifs <;> omega

lemma cycle_square_four_colorable_except_five_color_val_ne_add_two
    (a b n : ℕ) (hn : 3 * a + 4 * b = n) (hn3 : 3 ≤ n) (k : ℕ) (hk : k < n) :
    cycle_square_four_colorable_except_five_color_val a k ≠
      cycle_square_four_colorable_except_five_color_val a ((k + 2) % n) := by
  dsimp [cycle_square_four_colorable_except_five_color_val]
  rcases lt_or_ge (k + 2) n with hk2 | hk2
  · have h1 : (k + 2) % n = k + 2 := Nat.mod_eq_of_lt hk2
    rw [h1]
    split_ifs <;> omega
  · rcases eq_or_lt_of_le hk2 with heq | hgt
    · have h1 : (k + 2) % n = 0 := by
        rw [heq, Nat.mod_self]
      rw [h1]
      split_ifs <;> omega
    · have h1 : (k + 2) % n = 1 := by
        have : k + 2 = 1 + n := by omega
        rw [this, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [h1]
      split_ifs <;> omega

lemma cycle_square_four_colorable_except_five_exists_rep
    (n : ℕ) (hn : 3 ≤ n) (h5 : n ≠ 5) :
    ∃ a b : ℕ, 3 * a + 4 * b = n := by
  have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · use n / 3, 0; omega
  · use (n - 4) / 3, 1; omega
  · use (n - 8) / 3, 2; omega

theorem cycle_square_four_colorable_except_five
    (n : ℕ) [NeZero n] (hn : 3 ≤ n) (hfive : n ≠ 5) :
    ∃ c : Fin n → Fin 4,
      ∀ i, c i ≠ c (i+1) ∧ c i ≠ c (i+2) := by
  obtain ⟨a, b, hab⟩ := cycle_square_four_colorable_except_five_exists_rep n hn hfive
  let c : Fin n → Fin 4 := fun i =>
    ⟨cycle_square_four_colorable_except_five_color_val a i.val,
     cycle_square_four_colorable_except_five_color_val_lt_four a i.val⟩
  use c
  intro i
  constructor
  · intro h
    have hval : (c i).val = (c (i + 1)).val := by rw [h]
    dsimp [c] at hval
    have h1 : (i + 1 : Fin n).val = (i.val + 1) % n := by
      rw [Fin.val_add]
      have : (1 : Fin n).val = 1 := Nat.mod_eq_of_lt (by show 1 < n; omega)
      rw [this]
    rw [h1] at hval
    exact cycle_square_four_colorable_except_five_color_val_ne_add_one a b n hab i.val i.is_lt hval
  · intro h
    have hval : (c i).val = (c (i + 2)).val := by rw [h]
    dsimp [c] at hval
    have h2 : (i + 2 : Fin n).val = (i.val + 2) % n := by
      rw [Fin.val_add]
      have : (2 : Fin n).val = 2 := Nat.mod_eq_of_lt (by show 2 < n; omega)
      rw [this]
    rw [h2] at hval
    exact cycle_square_four_colorable_except_five_color_val_ne_add_two a b n hab hn i.val i.is_lt hval
