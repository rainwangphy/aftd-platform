import AFTD.Prelude

/-!
# op1525_multipartite_common_card_orientation_counterexample

Topic: combinatorics   Node: 3291a15c683a

Provenance: helper lemma. The 16-vertex counterexample to choosing an arbitrary common card in the multipartite route for OP-1525.

There are distinct four-entry triple-block profiles related by reversal with the same total numbers of blocks and true vertices and the same mixed-pair score, while singleton-block profiles with three true and one false vertex become self-reversing after one switch.
-/

theorem op1525_multipartite_common_card_orientation_counterexample :
    ∃ (p q : Fin 4 → ℕ) (s c : Fin 2 → ℕ),
      p ≠ q ∧
      (∀ j : Fin 4, p j = q j.rev) ∧
      (∑ j : Fin 4, p j) = 4 ∧ (∑ j : Fin 4, q j) = 4 ∧
      (∑ j : Fin 4, j.val * p j) = 6 ∧
      (∑ j : Fin 4, j.val * q j) = 6 ∧
      (∑ j : Fin 4, j.val * (3 - j.val) * p j) = 6 ∧
      (∑ j : Fin 4, j.val * (3 - j.val) * q j) = 6 ∧
      s 0 = 1 ∧ s 1 = 3 ∧
      c 0 = 2 ∧ c 1 = 2 ∧
      (∀ j : Fin 2, c j = c j.rev) ∧
      s ≠ (fun j => s j.rev) := by
  refine ⟨![0, 3, 0, 1], ![1, 0, 3, 0], ![1, 3], ![2, 2], ?_⟩
  decide
