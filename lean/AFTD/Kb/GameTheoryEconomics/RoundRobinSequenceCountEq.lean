import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence

/-!
# round_robin_sequence_count_eq

Topic: fair_division   Node: 0d4342bb2fce

Provenance: helper lemma. step towards round_robin_alpha_three_eq_two_thirds

The number of times agent a appears in the Round-Robin sequence of n agents and m goods is (m + (n - 1 - a)) / n.
-/

lemma round_robin_sequence_count_eq_dvd_eq_self {n Y : ℕ} (h1 : 0 < Y) (h2 : Y < 2 * n) (hdiv : n ∣ Y) : Y = n := by
  rcases hdiv with ⟨k, rfl⟩
  have hk_lt : k < 2 := by
    by_contra! h
    have : 2 * n ≤ n * k := by
      calc 2 * n = n * 2 := by ring
      _ ≤ n * k := Nat.mul_le_mul_left n h
    omega
  have hk_pos : 0 < k := by
    by_contra! h
    have : k = 0 := by omega
    subst this
    simp at h1
  have : k = 1 := by omega
  subst this
  simp

lemma round_robin_sequence_count_eq_dvd_iff (n m a : ℕ) (hn : 0 < n) (ha : a < n) :
    (n ∣ (m + (n - 1 - a) + 1)) ↔ m % n = a := by
  have H : m + (n - 1 - a) + 1 = n * (m / n) + (m % n + (n - 1 - a) + 1) := by
    have := Nat.div_add_mod m n
    omega
  rw [H, Nat.dvd_add_right (dvd_mul_right n (m / n))]
  have hr : m % n < n := Nat.mod_lt m hn
  have h1 : 0 < m % n + (n - 1 - a) + 1 := by omega
  have h2 : m % n + (n - 1 - a) + 1 < 2 * n := by omega
  constructor
  · intro hdvd
    have := round_robin_sequence_count_eq_dvd_eq_self h1 h2 hdvd
    omega
  · rintro rfl
    have : m % n + (n - 1 - m % n) + 1 = n := by omega
    rw [this]

lemma round_robin_sequence_count_eq_succ (n m : ℕ) [NeZero n] :
    round_robin_sequence n (m + 1) = (round_robin_sequence n m).concat ⟨m % n, Nat.mod_lt _ (NeZero.pos n)⟩ := by
  unfold round_robin_sequence
  rw [List.ofFn_succ']
  congr 1

/-- Exact pick count of an agent in the Round-Robin sequence: agent a picks (m + n - 1 - a)/n times. -/
theorem round_robin_sequence_count_eq (n m : ℕ) [NeZero n] (a : Fin n) :
    (round_robin_sequence n m).count a = (m + (n - 1 - a.val)) / n := by
  induction m with
  | zero =>
    have : (round_robin_sequence n 0) = [] := by
      unfold round_robin_sequence
      rfl
    rw [this]
    simp only [List.count_nil]
    have ha : a.val < n := a.isLt
    have hn : 0 < n := NeZero.pos n
    have : 0 + (n - 1 - a.val) < n := by omega
    rw [Nat.div_eq_of_lt this]
  | succ m ih =>
    rw [round_robin_sequence_count_eq_succ]
    rw [List.concat_eq_append, List.count_append, ih]
    rw [List.count_singleton]
    have h_count_sing : (if (⟨m % n, Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n) == a then 1 else 0) =
        (if m % n = a.val then 1 else 0) := by
      split_ifs with h1 h2 h3
      · rfl
      · exfalso
        apply h2
        rw [beq_iff_eq, Fin.ext_iff] at h1
        exact h1
      · exfalso
        apply h1
        rw [beq_iff_eq, Fin.ext_iff]
        exact h3
      · rfl
    rw [h_count_sing]
    have h_succ_div : (m + 1 + (n - 1 - a.val)) / n =
        (m + (n - 1 - a.val)) / n + if n ∣ (m + (n - 1 - a.val) + 1) then 1 else 0 := by
      have : m + 1 + (n - 1 - a.val) = (m + (n - 1 - a.val)) + 1 := by omega
      rw [this, Nat.succ_div]
    rw [h_succ_div]
    have h_dvd := round_robin_sequence_count_eq_dvd_iff n m a.val (NeZero.pos n) a.isLt
    simp only [h_dvd]
