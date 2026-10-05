import AFTD.Prelude
import AFTD.Kb.Tcs.IsResolutionDerivation
import AFTD.Kb.Tcs.CnfLit

/-!
# is_resolution_refutation

Topic: proof_complexity   Node: ef64c86d0e5f

A resolution refutation of F is a resolution derivation from F whose last clause is the empty clause; its length is the number of clauses in the sequence.
-/

/-- A resolution refutation of F: a resolution derivation from F ending in the empty clause. -/
def is_resolution_refutation {V : Type*} (F : Finset (Finset (CnfLit V))) (π : List (Finset (CnfLit V))) : Prop :=
  is_resolution_derivation F π ∧ π.getLast? = some ∅
