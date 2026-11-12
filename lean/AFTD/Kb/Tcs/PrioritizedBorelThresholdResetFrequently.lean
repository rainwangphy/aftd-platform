import AFTD.Prelude

/-!
# prioritized_borel_threshold_reset_frequently

Topic: automata   Node: 2d86a93e3074

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2, Proposition 41; s+1-state threshold controller for the paper’s lower-bound game.

For positive inputs bounded by s and a memory value initially zero that updates to the input when it exceeds memory and resets to zero otherwise, reset steps occur arbitrarily late.
-/

theorem prioritized_borel_threshold_reset_frequently
    (s : ℕ) (f m : ℕ → ℕ) (hf : ∀ n, 1 ≤ f n ∧ f n ≤ s)
    (hinit : m 0 = 0)
    (hstep : ∀ n, m (n+1) = if m n < f n then f n else 0) :
    ∀ N, ∃ n ≥ N, f n ≤ m n := by
  have hm : ∀ n, m n ≤ s := by
    intro n
    cases n with
    | zero => rw [hinit]; omega
    | succ n => rw [hstep]; split_ifs <;> have := (hf n).2 <;> omega
  intro N
  by_contra h
  push_neg at h
  have hincr : ∀ n, N ≤ n → m n < m (n+1) := by
    intro n hn
    have hn' := h n hn
    rw [hstep, if_pos (by omega)]
    omega
  have hind : ∀ j, j ≤ m (N+j) := by
    intro j
    induction j with
    | zero => omega
    | succ j ih =>
      have hi := hincr (N+j) (by omega)
      have heq : N + (j+1) = (N+j)+1 := by omega
      rw [heq]
      omega
  have := hind (s+1)
  have := hm (N+(s+1))
  omega
