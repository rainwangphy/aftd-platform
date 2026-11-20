import AFTD.Prelude
import AFTD.Kb.Tcs.TreelikeCpDerivation
import AFTD.Kb.Tcs.CnfLit
import AFTD.Kb.Tcs.LinIneqUnarySize
import AFTD.Kb.Tcs.LinIneq
import AFTD.Kb.Tcs.CnfClauseToLin
import AFTD.Kb.Tcs.CnfLitDecidableEq

/-!
# treelike_cp_size

Topic: proof_complexity   Node: 5196e931bf59

Provenance: formalization of a published result. Source: arXiv:2611.24548 Sec 2.1 & Def 4.1

The unary size of a treelike Cutting Planes derivation tree d, defined recursively as 1 plus the unary size lin_ineq_unary_size L of the root inequality L, plus the sum of treelike_cp_size over all direct sub-derivations.
-/

/-- Unary size of a treelike Cutting Planes derivation tree. -/
def treelike_cp_size {n : ℕ} {F : List (List (CnfLit (Fin n)))} {L : LinIneq n} (d : TreelikeCpDerivation n F L) : ℕ := 1 + lin_ineq_unary_size L +
  match d with
  | .trivial => 0
  | .box_lower _ => 0
  | .box_upper _ => 0
  | .clause _ _ => 0
  | .lin_comb d₁ d₂ _ _ => treelike_cp_size d₁ + treelike_cp_size d₂
  | .division d _ _ _ _ => treelike_cp_size d
