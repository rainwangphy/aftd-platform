import AFTD.Prelude

/-!
# manyOneReducible_compl

Topic: computability   Node: 5c64349aff2a

If a predicate p many-one reduces to q, then the complement of p many-one reduces to the complement of q.
-/

/-- Many-one reducibility is preserved under taking complements. -/
theorem manyOneReducible_compl {α β : Type*} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} (h : p ≤₀ q) : (fun a => ¬p a) ≤₀ (fun b => ¬q b) := by
  rcases h with ⟨f, hf, hred⟩
  exact ⟨f, hf, fun a => not_congr (hred a)⟩
