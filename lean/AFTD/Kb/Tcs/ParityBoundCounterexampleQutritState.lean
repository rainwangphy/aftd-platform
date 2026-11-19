import AFTD.Prelude

/-!
# parity_bound_counterexample_qutrit_state

Topic: quantum   Node: d5e343f11484

Provenance: helper lemma. step towards open_problem_735_parity_bound_higher_dimension

The cross-source-correlated qutrit state of the counterexample: for n = 3 sources of dimension 3 and a trivial central space (m = 1), the diagonal matrix putting weight 1/2 on the constant string (0,0,0) and weight 1/2 on the constant string (1,1,1).
-/

/-- Cross-source-correlated qutrit state witness: diagonal with weight 1/2 on the constant strings (0,0,0) and (1,1,1) of (Fin 3 → Fin 3) and trivial central factor Fin 1. -/
noncomputable def parity_bound_counterexample_qutrit_state : Matrix ((Fin 3 → Fin 3) × Fin 1) ((Fin 3 → Fin 3) × Fin 1) ℂ := Matrix.diagonal (fun p => if p.1 = (fun _ => (0 : Fin 3)) then (1 / 2 : ℂ) else if p.1 = (fun _ => (1 : Fin 3)) then (1 / 2 : ℂ) else 0)
