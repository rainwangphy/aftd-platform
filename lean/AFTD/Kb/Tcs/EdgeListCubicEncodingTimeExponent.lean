import AFTD.Prelude

/-!
# edge_list_cubic_encoding_time_exponent

Topic: algorithms   Node: d8387b90fd9a

Provenance: helper lemma. arXiv:2610.35794, Conjecture 5 (calibrating the time bound to n)

For every natural number n, the integer square root of ⌊2·⌊(3n²+3n)/2⌋/3⌋ equals n. (A cubic edge list on n vertices has unary encoding length N = (3n²+3n)/2, so the exponent ⌊√⌊2N/3⌋⌋ in the time bound of the O*(2^n) question is exactly n.)
-/

theorem edge_list_cubic_encoding_time_exponent (n : ℕ) :
    Nat.sqrt (2 * ((3 * n ^ 2 + 3 * n) / 2) / 3) = n := by
  have h : 2 * ((3 * n ^ 2 + 3 * n) / 2) = 3 * n ^ 2 + 3 * n := by
    have : 2 ∣ 3 * n ^ 2 + 3 * n := by
      have := Nat.even_mul_succ_self n
      rw [show 3 * n ^ 2 + 3 * n = 3 * (n * (n + 1)) by ring]
      exact Dvd.dvd.mul_left (even_iff_two_dvd.mp this) 3
    exact Nat.mul_div_cancel' this
  rw [h, show 3 * n ^ 2 + 3 * n = 3 * (n * n + n) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  exact Nat.sqrt_add_eq n (by omega)
