import AFTD.Prelude

/-!
# re_of_manyOneReducible

Topic: computability   Node: cd7cda917b08

Provenance: formalization of a published result. Source: standard textbook result (computability theory: many-one reductions preserve recursive enumerability)

If `p` is many-one reducible to `q` and `q` is recursively enumerable, then `p` is recursively enumerable.
-/

/-- Recursive enumerability is preserved backwards under many-one reductions. -/
theorem re_of_manyOneReducible {α β : Type*} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} (h₁ : p ≤₀ q) (h₂ : REPred q) : REPred p := by
  obtain ⟨f, hf, hpq⟩ := h₁
  have hqf : REPred (q ∘ f) := Partrec.comp h₂ hf
  exact REPred.of_eq hqf fun a => (hpq a).symm
