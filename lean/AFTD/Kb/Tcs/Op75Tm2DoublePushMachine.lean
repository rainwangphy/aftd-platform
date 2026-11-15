import AFTD.Prelude

/-!
# op75_tm2_double_push_machine

Topic: np_completeness   Node: 2c80e5868bf0

Provenance: helper lemma. OP-75 Karp-reduction composition: finite-statement stack-growth bound in the repository TM2 model.

A finite one-stack TM2 whose single statement pushes true twice and then halts.
-/

def op75_tm2_double_push_machine : Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := Turing.TM2.Stmt.push () (fun _ => true)
    (Turing.TM2.Stmt.push () (fun _ => true) Turing.TM2.Stmt.halt)
