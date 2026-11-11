import AFTD.Prelude
import AFTD.Kb.Physics.DephasedTreeLocalNoiseCriterion

/-!
# dephased_tree_two_positive_neighbors_degree_two

Topic: quantum_mechanics   Node: 0ebbadcedf57

Provenance: helper lemma. Structural support-path reduction for OP-827, tested exhaustively through 10 vertices in experiment 22387.

Under the local noise criterion, a vertex with two distinct positive-parameter neighbors has degree exactly two and itself has positive parameter.
-/

theorem dephased_tree_two_positive_neighbors_degree_two {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj] (q : V → ℝ) (hlocal : dephased_tree_local_noise_criterion T q) (v u w : V) (hne : u ≠ w) (hu : T.Adj v u) (hw : T.Adj v w) (hqu : 0 < q u) (hqw : 0 < q w) : T.degree v = 2 ∧ 0 < q v := by
  classical
  have hdeg : 2 ≤ T.degree v := by
    have hcard : ({u,w} : Finset V).card = 2 := by simp [hne]
    have hsub : ({u,w} : Finset V) ⊆ T.neighborFinset v := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simpa using hu
      · simpa using hw
    have hh := Finset.card_le_card hsub
    rw [hcard] at hh
    simpa using hh
  rcases hlocal with ⟨htwo,hbranch⟩
  have hdegree : T.degree v = 2 := by
    by_contra h
    exact hne (hbranch v (by omega) u w hu hw hqu hqw)
  refine ⟨hdegree,?_⟩
  have hbound := htwo v hdegree u w hne hu hw
  have hprod : 0 < q u * q w := mul_pos hqu hqw
  linarith
