import AFTD.Prelude
import AFTD.Kb.Tcs.IsCsymMatrix

/-!
# simple_graph_csym_max_nullity

Topic: graphs   Node: d8d7964fdc5c

Provenance: formalization of a published result. Source: arXiv:2611.01102 Sec. 1, line 121

The combinatorially symmetric maximum nullity N(G) of a finite simple graph G is the supremum of the nullities of all real matrices A associated with G that are combinatorially symmetric.
-/

/-- The maximum nullity N(G) of a combinatorially symmetric real matrix whose graph is G. -/
noncomputable def simple_graph_csym_max_nullity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ := sSup { k : ℕ | ∃ A : Matrix V V ℝ, is_csym_matrix G A ∧ Module.finrank ℝ A.mulVecLin.ker = k }
