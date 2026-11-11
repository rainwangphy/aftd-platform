import AFTD.Prelude
import AFTD.Kb.Physics.DephasedTreeLocalNoiseCriterion

/-!
# dephased_tree_zero_vertex_positive_neighbor_unique

Topic: quantum_mechanics   Node: e828442ed406

Provenance: helper lemma. Structural reduction of OP-827 to positive-support paths and zero-parameter leaves.

Under the local noise criterion, a zero-parameter vertex has at most one positive-parameter neighbor.
-/

theorem dephased_tree_zero_vertex_positive_neighbor_unique {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj] (q : V → ℝ) (hlocal : dephased_tree_local_noise_criterion T q) (v u w : V) (hv : q v = 0) (hu : T.Adj v u) (hw : T.Adj v w) (hqu : 0 < q u) (hqw : 0 < q w) : u = w := by
  classical
  by_contra hne
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
  by_cases htwo' : T.degree v = 2
  · have hbound := htwo v htwo' u w hne hu hw
    rw [hv] at hbound
    have hprod : 0 < q u * q w := mul_pos hqu hqw
    linarith
  · exact hne (hbranch v (by omega) u w hu hw hqu hqw)
