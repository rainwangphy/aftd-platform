import AFTD.Prelude
import AFTD.Kb.Tcs.BpeSteps
import AFTD.Kb.Tcs.BpeGreedyStep
import AFTD.Kb.Tcs.BpeGreedyStepLengthLe

/-!
# bpe_greedy_steps_length_le

Topic: algorithms   Node: 6df3d5cfa48f

Provenance: helper lemma. arXiv:2611.08671

Applying k greedy full byte-pair merge steps to a string produces an output string of length at most the input string length.
-/

/-- Any sequence of k greedy BPE merge steps produces an output string of length at most the initial string length. -/
theorem bpe_greedy_steps_length_le (k : ℕ) (s t : List ℕ) (h : bpe_steps bpe_greedy_step k s t) : t.length ≤ s.length := by
  induction k generalizing s with
  | zero =>
    simp only [bpe_steps] at h
    subst h
    exact le_rfl
  | succ k ih =>
    obtain ⟨u, hsu, hut⟩ := h
    have h1 := bpe_greedy_step_length_le s u hsu
    have h2 := ih u hut
    exact le_trans h2 h1
