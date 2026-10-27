import AFTD.Prelude
import AFTD.Kb.Tcs.ThirdPrincipalSpecialization

/-!
# third_principal_specialization_eval_one

Topic: graphs   Node: 801e1e7feec5

Provenance: helper lemma. step towards caterpillar_third_t_chromatic_specialization_fiber_le_two

Evaluating the third principal specialization of a graph G at (1, 1) via MvPolynomial.eval (fun _ => 1) equals the number of proper 3-colorings Fintype.card (G.Coloring (Fin 3)).
-/

/-- Evaluating third_principal_specialization at (1, 1) yields the number of proper 3-colorings. -/
theorem third_principal_specialization_eval_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    MvPolynomial.eval (fun _ : Fin 2 => (1 : ℤ)) (third_principal_specialization G) =
      Fintype.card (G.Coloring (Fin 3)) := by
  unfold third_principal_specialization
  rw [map_sum]
  simp
