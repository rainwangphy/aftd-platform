import AFTD.Prelude

/-!
# qary_run_count_ge

Topic: information   Node: 5456c1f7bc63

Provenance: helper lemma. step towards op_1534_constant_word_all_deletion_embedding_convex_order

The number of maximal constant runs of the word y whose length is at least k. Position i starts a maximal run when i = 0 or the immediate predecessor y(i-1) differs from y(i); that run has length ≥ k when i+k ≤ n and every position i..i+k-1 carries the letter y i.
-/

/-- Number of maximal constant runs of y (over any decidable-equality alphabet) of length at least k. -/
def qary_run_count_ge {n : ℕ} {α : Type} [DecidableEq α] (y : Fin n → α) (k : ℕ) : ℕ := ((Finset.univ : Finset (Fin n)).filter (fun i => (∀ j : Fin n, j.val + 1 = i.val → y j ≠ y i) ∧ (i.val + k ≤ n) ∧ (∀ j : Fin n, i ≤ j → j.val < i.val + k → y j = y i))).card
