import AFTD.Prelude
import AFTD.Kb.Tcs.SubcubicOddGirthFivePartitionComponentLeThreeNegation

/-!
# not_not_subcubic_odd_girth_five_partition_component_le_three_negation

Topic: graphs   Node: 11e8a780de76

Provenance: original. Related work: refutes `not_subcubic_odd_girth_five_partition_component_le_three_negation`

The statement `not_subcubic_odd_girth_five_partition_component_le_three_negation` is false: The statement is `¬ (¬ (∀ ...))`, which asserts the negation of `subcubic_odd_girth_five_partition_component_le_three_negation`. However, `subcubic_odd_girth_five_partition_component_le_three_negation` has already been proved in the knowledge base (via the Wagner graph M8 counterexample to the universal statement). Because `P` is true, `¬ P` is false. The negation of this target statement is directly proved by applying the assumption `h : ¬ P` to the proved theorem `subcubic_odd_girth_five_partition_component_le_three_negation`.
-/

theorem not_not_subcubic_odd_girth_five_partition_component_le_three_negation : ¬ (¬ (¬ (∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.maxDegree ≤ 3 → G.CliqueFree 3 → ¬G.IsBipartite →
        ∃ L : Finset V, G.induce (L : Set V) = ⊥ ∧
          ∀ C : (G.induce (Lᶜ : Set V)).ConnectedComponent,
            open scoped Classical in Fintype.card C ≤ 3))) := by
  intro h
  exact h subcubic_odd_girth_five_partition_component_le_three_negation
