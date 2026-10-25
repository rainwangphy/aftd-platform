import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaElementaryCellStep

/-!
# alpha_elementary_cell_step_length_parity

Topic: combinatorics   Node: b9ac9cd0c5d4

Provenance: helper lemma. Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

One elementary operation reverses the parity of the number of cells (source Lemma 2.3).
-/

theorem alpha_elementary_cell_step_length_parity (a b : List ℕ) (i : ℕ) (h : alpha_elementary_cell_step a b i) : b.length % 2 = (a.length + 1) % 2 := by
  rcases h with ⟨hi, hsplit | hconj⟩
  · rcases hsplit with ⟨_, rfl⟩
    simp only [List.length_append, List.length_take, List.length_drop, List.length_cons, List.length_nil]
    omega
  · rcases hconj with ⟨hi0, _, rfl⟩
    simp only [List.length_append, List.length_take, List.length_drop, List.length_cons, List.length_nil]
    omega
