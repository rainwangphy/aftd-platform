import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixCutNorm

/-!
# graph_cut_dist

Topic: graphs   Node: f20f1d685696

Provenance: formalization of a published result. Source: arXiv:2611.05048, Section 1

The unnormalized cut distance d_□(G, H) between two simple graphs G and H on the same finite vertex set V is the minimum over all bijections π : V ≃ V of the cut norm of the difference matrix A_G^π - A_H.
-/

/-- The unnormalized cut distance d_□(G, H) between two simple graphs on the same finite vertex set V is the minimum over all bijections π of the cut norm of A_G^π - A_H. -/
noncomputable def graph_cut_dist {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) : ℝ := by
  classical
  exact (Finset.univ : Finset (Equiv.Perm V)).inf' ⟨Equiv.refl V, Finset.mem_univ _⟩
    (fun π => matrix_cut_norm (fun v v' =>
      (if G.Adj v v' then (1 : ℝ) else 0) - (if H.Adj (π v) (π v') then 1 else 0)))
