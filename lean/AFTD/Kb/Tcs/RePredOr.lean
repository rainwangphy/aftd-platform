import AFTD.Prelude

/-!
# re_pred_or

Topic: computability   Node: 1bba540f6e2c

Provenance: formalization of a published result. Source: standard textbook result (computability theory: RE sets are closed under union)

If p and q are recursively enumerable predicates, then their disjunction fun a => p a ∨ q a is recursively enumerable.
-/

/-- The disjunction of two recursively enumerable predicates is recursively enumerable. -/
theorem re_pred_or {α : Type*} [Primcodable α] {p q : α → Prop} (hp : REPred p) (hq : REPred q) : REPred (fun a => p a ∨ q a) := by
  obtain ⟨k, hk, hdom⟩ := Partrec.merge' hp hq
  have h_re : REPred (fun a => (k a).Dom) := hk.dom_re
  refine h_re.of_eq fun a => ?_
  rw [(hdom a).2]
  simp [Part.assert]
