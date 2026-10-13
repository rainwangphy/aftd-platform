import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphFlipByMatrix
import AFTD.Kb.Tcs.DigraphIsAcyclic

/-!
# tournament_min_rank

Topic: graphs   Node: 37d951e6c1a1

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Sec. 2.2 (tournament minimum rank).

The tournament minimum rank tmr(D): the least F₂-rank of a symmetric matrix M over F₂ that decycles D, i.e. such that reversing every arc uv with M_uv = 1 makes D acyclic.
-/

/-- `tmr D`: least `𝔽₂`-rank of a symmetric decycling matrix of `D`. -/
noncomputable def tournament_min_rank {V : Type*} [Fintype V] (D : Digraph V) : ℕ :=
  sInf {r | ∃ M : Matrix V V (ZMod 2), M.IsSymm ∧
    digraph_is_acyclic (digraph_flip_by_matrix D M) ∧ M.rank = r}
