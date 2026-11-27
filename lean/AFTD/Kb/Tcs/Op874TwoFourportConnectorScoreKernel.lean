import AFTD.Prelude

/-!
# op874_two_fourport_connector_score_kernel

Topic: graphs   Node: 53c3e2529885

Provenance: helper lemma. Two-block matching-cut score table for OP-874; experiment 42552.

The conditional block cut-score table peaks only at the two complementary connector-bit assignments.
-/

theorem op874_two_fourport_connector_score_kernel :
  let A : Fin 16 → ℕ := ![12,10,14,12,12,12,12,12,12,12,12,12,12,14,10,12]
  let B : Fin 16 → ℕ := ![12,12,10,12,12,12,12,14,14,12,12,12,12,10,12,12]
  ∀ i : Fin 16, A i + B i ≤ 26 ∧ (A i + B i = 26 → i = 7 ∨ i = 8) := by decide
