import AFTD.Prelude
import AFTD.Kb.Tcs.SeidelMatrix

/-!
# seidel_matrix_row_sum_eq_degree

Topic: combinatorics   Node: f980211eebcc

Provenance: helper lemma. step towards ramsey_b63_b64_seidel_graph_exists

For a finite simple graph G with decidable adjacency and any vertex i, the i-th Seidel row sum equals |V| - 1 - 2·deg(i), where deg(i) is the number of neighbours of i.
-/

/-- The i-th row sum of the Seidel matrix of a finite graph is |V| - 1 - 2 * deg(i). -/
theorem seidel_matrix_row_sum_eq_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i : V) :
    ∑ j : V, seidel_matrix G i j
      = (Fintype.card V : ℤ) - 1 - 2 * (Fintype.card (G.neighborSet i) : ℤ) := by
  have hpt : ∀ j : V, seidel_matrix G i j
      = (if j = i then (0:ℤ) else 1) - 2 * (if G.Adj i j then (1:ℤ) else 0) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp [seidel_matrix, SimpleGraph.irrefl]
    · have hij : i ≠ j := fun h => hji h.symm
      simp only [seidel_matrix, Matrix.of_apply, hji, hij, if_false]
      by_cases ha : G.Adj i j <;> simp [ha]
  have hfirst : ∑ j : V, (if j = i then (0:ℤ) else 1) = (Fintype.card V : ℤ) - 1 := by
    have : ∑ j : V, (if j = i then (0:ℤ) else 1)
        = ∑ j : V, ((1:ℤ) - if j = i then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      split <;> simp
    rw [this, Finset.sum_sub_distrib]
    simp [Finset.sum_ite_eq', Finset.sum_const, Finset.card_univ]
  have hcard : (Fintype.card (G.neighborSet i) : ℤ) = ((Finset.univ.filter (fun j => G.Adj i j)).card : ℤ) := by
    rw [← Set.toFinset_card (G.neighborSet i), ← SimpleGraph.neighborFinset_def,
      SimpleGraph.neighborFinset_eq_filter]
  have hsecond : ∑ j : V, (if G.Adj i j then (1:ℤ) else 0) = (Fintype.card (G.neighborSet i) : ℤ) := by
    rw [show (∑ j : V, (if G.Adj i j then (1:ℤ) else 0))
          = ∑ j ∈ (Finset.univ : Finset V), (if G.Adj i j then (1:ℤ) else 0) by simp]
    rw [Finset.sum_boole, hcard]
  rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_sub_distrib, ← Finset.mul_sum, hfirst, hsecond]
