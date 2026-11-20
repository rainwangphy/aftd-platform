import AFTD.Prelude
import AFTD.Kb.Tcs.BpeOptimalUtility
import AFTD.Kb.Tcs.BpeSteps
import AFTD.Kb.Tcs.BpePartialStep
import AFTD.Kb.Tcs.BpePartialMerge

/-!
# bpe_optimal_utility_le_iff

Topic: algorithms   Node: eeb42559d2d4

Provenance: helper lemma. Helper for OP-1287: bounded natural supremum characterizes the comparator optimum.

The optimal utility of k partial merge steps is at most B exactly when every string reachable in k such steps has length reduction at most B.
-/

theorem bpe_ou_steps_refl : ∀ (k : ℕ) (s : List ℕ), bpe_steps bpe_partial_step k s s
  | 0, _ => rfl
  | k+1, s => ⟨s, Or.inl rfl, bpe_ou_steps_refl k s⟩

theorem bpe_optimal_utility_le_iff (s : List ℕ) (k B : ℕ) :
    bpe_optimal_utility s k ≤ B ↔
      ∀ t : List ℕ, bpe_steps bpe_partial_step k s t → s.length - t.length ≤ B := by
  unfold bpe_optimal_utility
  have hbdd : BddAbove {u : ℕ | ∃ t, bpe_steps bpe_partial_step k s t ∧ u = s.length - t.length} :=
    ⟨s.length, by rintro u ⟨t, -, rfl⟩; exact Nat.sub_le _ _⟩
  have hne : ({u : ℕ | ∃ t, bpe_steps bpe_partial_step k s t ∧ u = s.length - t.length}).Nonempty :=
    ⟨s.length - s.length, s, bpe_ou_steps_refl k s, rfl⟩
  constructor
  · intro h t ht
    exact le_trans (le_csSup hbdd ⟨t, ht, rfl⟩) h
  · intro h
    apply csSup_le hne
    rintro u ⟨t, ht, rfl⟩
    exact h t ht
