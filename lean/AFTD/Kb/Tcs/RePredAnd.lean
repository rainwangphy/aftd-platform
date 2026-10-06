import AFTD.Prelude

/-!
# re_pred_and

Topic: computability   Node: 7f85288ffbcb

Provenance: formalization of a published result. Source: standard textbook result (computability theory: RE sets are closed under intersection)

If p and q are recursively enumerable predicates, then their conjunction fun a => p a ∧ q a is recursively enumerable.
-/

/-- Conjunction of two recursively enumerable predicates is recursively enumerable. -/
theorem re_pred_and {α : Type*} [Primcodable α] {p q : α → Prop} (hp : REPred p) (hq : REPred q) : REPred (fun a => p a ∧ q a) := by
  have hg : Partrec₂ (fun (a : α) (_ : Unit) => Part.assert (q a) fun _ => Part.some ()) :=
    hq.comp Computable.fst
  have h := hp.bind hg
  refine h.of_eq fun a => ?_
  apply Part.ext
  intro u
  simp [Part.mem_assert_iff, Part.mem_bind_iff]
