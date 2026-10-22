import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphOutCount

/-!
# digraph_out_laplacian

Topic: graphs   Node: 351d0f4a2e82

Provenance: helper lemma. step towards tournament_arborescence_hadamard_bound

The out-degree Laplacian L_D of a digraph D on Fin n over ℝ: its diagonal entries are the out-degrees and its off-diagonal (i,j) entry is -1 when i → j and 0 otherwise (equivalently L_D = diag(out-degree) - A_D).
-/

/-- The out-degree Laplacian of a digraph on `Fin n`: out-degrees on the diagonal, `-1` at each arc, `0` elsewhere. -/
noncomputable def digraph_out_laplacian {n : ℕ} (D : Digraph (Fin n)) [DecidableRel D.Adj] : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => (digraph_out_count D i : ℝ)) - Matrix.of (fun i j => if D.Adj i j then (1 : ℝ) else 0)
