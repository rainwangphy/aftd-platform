import AFTD.Prelude
import AFTD.Kb.Tcs.ForestCarpoolTailEnvelope

/-!
# forest_carpool_fibonacci_envelope_decay

Topic: online_algorithms   Node: caa43621e370

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

At every level at least four the proposed tail envelope is at least the next-level envelope plus the square of the previous-level envelope.
-/

private lemma forest_carpool_fib_decay_shifted (n : ℕ) :
    (1 / 2 : ℝ) ^ Nat.fib (n + 5) +
      ((1 / 2 : ℝ) ^ Nat.fib (n + 3)) ^ 2 ≤
      (1 / 2 : ℝ) ^ Nat.fib (n + 4) := by
  have f3 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
    simpa [Nat.add_assoc] using (Nat.fib_add_two (n := n + 1))
  have f4 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
    simpa [Nat.add_assoc] using (Nat.fib_add_two (n := n + 2))
  have f5 : Nat.fib (n + 5) = Nat.fib (n + 3) + Nat.fib (n + 4) := by
    simpa [Nat.add_assoc] using (Nat.fib_add_two (n := n + 3))
  have fdouble : Nat.fib (n + 3) * 2 = Nat.fib (n + 4) + Nat.fib (n + 1) := by omega
  have p1 : (1 / 2 : ℝ) ^ Nat.fib (n + 1) ≤ 1 / 2 := by
    apply pow_le_of_le_one (by norm_num) (by norm_num)
    simp
  have p3 : (1 / 2 : ℝ) ^ Nat.fib (n + 3) ≤ 1 / 2 := by
    apply pow_le_of_le_one (by norm_num) (by norm_num)
    simp
  have e5 : (1 / 2 : ℝ) ^ Nat.fib (n + 5) =
      (1 / 2 : ℝ) ^ Nat.fib (n + 4) * (1 / 2 : ℝ) ^ Nat.fib (n + 3) := by
    rw [f5, pow_add, mul_comm]
  have e3 : ((1 / 2 : ℝ) ^ Nat.fib (n + 3)) ^ 2 =
      (1 / 2 : ℝ) ^ Nat.fib (n + 4) * (1 / 2 : ℝ) ^ Nat.fib (n + 1) := by
    rw [← pow_mul, fdouble, pow_add]
  rw [e5, e3]
  calc
    _ = (1 / 2 : ℝ) ^ Nat.fib (n + 4) *
        ((1 / 2 : ℝ) ^ Nat.fib (n + 3) + (1 / 2 : ℝ) ^ Nat.fib (n + 1)) := by ring
    _ ≤ (1 / 2 : ℝ) ^ Nat.fib (n + 4) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

theorem forest_carpool_fibonacci_envelope_decay (k : ℕ) (hk : 4 ≤ k) : forest_carpool_tail_envelope (k + 1) + forest_carpool_tail_envelope (k - 1) ^ 2 ≤ forest_carpool_tail_envelope k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa [forest_carpool_tail_envelope, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using forest_carpool_fib_decay_shifted n
