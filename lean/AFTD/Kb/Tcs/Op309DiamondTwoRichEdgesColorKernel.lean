import AFTD.Prelude

/-!
# op309_diamond_two_rich_edges_color_kernel

Topic: graphs   Node: ea07285c7c24

Provenance: helper lemma. Finite normalized color kernel for the diamond obstruction in OP-309; experiment 33495.

Three values from a five-color palette cannot all avoid colors 0, 1 and 2 and also be pairwise distinct.
-/

theorem op309_diamond_two_rich_edges_color_kernel :
    ∀ d e f : Fin 5,
      (d ≠ 0 ∧ d ≠ 1 ∧ d ≠ 2) →
      (e ≠ 0 ∧ e ≠ 1 ∧ e ≠ 2) →
      (f ≠ 0 ∧ f ≠ 1 ∧ f ≠ 2) →
      d ≠ e → d ≠ f → e ≠ f → False := by
  decide
