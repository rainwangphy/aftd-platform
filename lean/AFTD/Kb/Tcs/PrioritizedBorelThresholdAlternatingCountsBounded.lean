import AFTD.Prelude

/-!
# prioritized_borel_threshold_alternating_counts_bounded

Topic: automata   Node: 7980fc744d9b

Provenance: helper lemma.

In the smallest threshold-strategy fork, on the fixed alternating c1,c2 branch, the recurrence counting compatible hidden histories has at most one history in each state-and-memory bucket at every depth. Thus the conjectured growth on that particular branch is false.
-/

structure In784Counts where
  h0 : ℕ
  h1 : ℕ
  p0 : ℕ
  p1 : ℕ
  q0 : ℕ
  q1 : ℕ
  deriving DecidableEq

def in784_count_step (c : In784Counts) (b : Bool) : In784Counts :=
  ⟨c.q0, c.q1, if b then c.h0 else 0, if b then c.h1 else 0,
   c.q0 + if b then c.p1 else 0, c.q1 + if b then 0 else c.p0⟩

def in784_count_run : ℕ → In784Counts
  | 0 => ⟨1, 0, 0, 0, 0, 0⟩
  | n + 1 => in784_count_step (in784_count_run n) (decide (n % 2 = 0))

theorem in784_alternating_pair : ∀ n,
    in784_count_run (2*n+4) = ⟨0, 1, 0, 0, 0, 1⟩ ∧
    in784_count_run (2*n+5) = ⟨0, 1, 0, 1, 0, 1⟩ := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
      rcases ih with ⟨heven, hodd⟩
      have heq1 : 2 * (n+1) + 4 = (2*n+5)+1 := by omega
      have heq2 : 2 * (n+1) + 5 = (2*n+6)+1 := by omega
      have hmod1 : (2*n+5) % 2 = 1 := by omega
      have hmod2 : (2*n+6) % 2 = 0 := by omega
      have hnext : in784_count_run (2*n+6) = ⟨0, 1, 0, 0, 0, 1⟩ := by
        have hn : 2*n+6 = (2*n+5)+1 := by omega
        rw [hn, in784_count_run, hodd]
        simp [in784_count_step, hmod1]
      constructor
      · rw [show 2 * (n+1) + 4 = 2*n+6 by omega]
        exact hnext
      · rw [heq2, in784_count_run, hnext]
        simp [in784_count_step, hmod2]

theorem prioritized_borel_threshold_alternating_counts_bounded :
    ∀ n, (in784_count_run n).h0 ≤ 1 ∧ (in784_count_run n).h1 ≤ 1 ∧
      (in784_count_run n).p0 ≤ 1 ∧ (in784_count_run n).p1 ≤ 1 ∧
      (in784_count_run n).q0 ≤ 1 ∧ (in784_count_run n).q1 ≤ 1 := by
  intro n
  by_cases hsmall : n < 4
  · interval_cases n <;> decide
  · obtain ⟨m, hm⟩ : ∃ m, n = 2*m+4 ∨ n = 2*m+5 := by
      refine ⟨(n-4)/2, ?_⟩
      omega
    rcases hm with rfl | rfl
    · rw [(in784_alternating_pair m).1]
      decide
    · rw [(in784_alternating_pair m).2]
      decide
