import AFTD.Prelude

/-!
# op75_tm2_pushes

Topic: np_completeness   Node: 2cffa5813eb7

Provenance: helper lemma. OP-75 Karp-reduction composition: finite-statement stack-growth bound in the repository TM2 model.

A syntactic upper bound on how many pushes a single TM2 statement can execute, using a maximum at branches.
-/

def op75_tm2_pushes {K : Type} {Γ : K → Type} {Λ σ : Type} : Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => op75_tm2_pushes q + 1
  | .peek _ _ q => op75_tm2_pushes q
  | .pop _ _ q => op75_tm2_pushes q
  | .load _ q => op75_tm2_pushes q
  | .branch _ q r => max (op75_tm2_pushes q) (op75_tm2_pushes r)
  | .goto _ => 0
  | .halt => 0
