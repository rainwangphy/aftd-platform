import AFTD.Prelude

/-!
# draft_enum_order

Topic: fair_division   Node: 15fd61e1fc81

Provenance: helper lemma. step towards draft_rule_characterization

The linear order on objects induced by an enumeration e : Object ≃ Fin T, listing e.symm 0 as the best object and e.symm (T-1) as the worst. This is the "common ranking" of a unanimous profile written by means of a bijection.
-/

/-- The order of a unanimous profile induced by a bijection Object ≃ Fin T, best object first. -/
def draft_enum_order {Object : Type*} [DecidableEq Object] {T : ℕ} (e : Object ≃ Fin T) : LinearOrder Object := @Equiv.linearOrder Object (Fin T) (e.trans (Fin.revPerm)) _ _
