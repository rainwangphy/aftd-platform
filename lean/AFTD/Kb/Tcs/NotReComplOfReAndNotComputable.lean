import AFTD.Prelude

/-!
# not_re_compl_of_re_and_not_computable

Topic: computability   Node: c4b375378e83

Provenance: formalization of a published result. Source: standard textbook result (computability theory: Post's theorem, a set is decidable iff it and its complement are RE)

If a predicate is recursively enumerable but undecidable, then its complement is not recursively enumerable (Post's theorem).
-/

/-- The complement of an undecidable recursively enumerable predicate is not recursively enumerable. -/
theorem not_re_compl_of_re_and_not_computable {α : Type*} [Primcodable α] {p : α → Prop} (hre : REPred p) (hnc : ¬ComputablePred p) : ¬REPred (fun a => ¬p a) := fun hrec => hnc (ComputablePred.computable_iff_re_compl_re'.2 ⟨hre, hrec⟩)
