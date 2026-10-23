import AFTD.Prelude
import AFTD.Kb.Tcs.CnfLit

/-!
# cnf_lit_decidable_eq

Topic: proof_complexity   Node: 78f6c7800d5d

Provenance: helper lemma. step towards resolution_fpt_incidence_treewidth

Decidable equality on CNF literals, derived from decidable equality on the underlying variables.
-/

/-- Decidable equality on `CnfLit V` for `[DecidableEq V]`. -/
instance cnf_lit_decidable_eq {V : Type*} [DecidableEq V] : DecidableEq (CnfLit V) := fun a b => match a, b with
  | .pos u, .pos v => decidable_of_iff (u = v) ⟨fun h => by rw [h], fun h => by cases h; rfl⟩
  | .pos _, .neg _ => isFalse (by intro h; cases h)
  | .neg _, .pos _ => isFalse (by intro h; cases h)
  | .neg u, .neg v => decidable_of_iff (u = v) ⟨fun h => by rw [h], fun h => by cases h; rfl⟩
