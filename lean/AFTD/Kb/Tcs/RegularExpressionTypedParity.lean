import AFTD.Prelude

/-!
# regular_expression_typed_parity

Topic: automata   Node: b24c2287474f

Provenance: formalization of a published result. Source: arXiv:2610.11717 (Every Regular Language Has a Bipartite Cactus Automaton), Sec. 3.1 (parity typing).

A regular expression is typed with parity p ∈ ℤ/2 by the rules: ∅ may be given either parity, ε has parity 0, every letter has parity 1, a union of two expressions of parity p has parity p, a concatenation of expressions of parities p and q has parity p+q, and the star of an expression of parity 0 has parity 0 (no other star is typable).
-/

/-- `r` is typed with parity `p`: built by the parity typing rules (∅ either parity, ε parity 0, letters parity 1, unions of equal parity, concatenation adds parities, star only of parity-0 expressions, with parity 0). -/
def regular_expression_typed_parity {α : Type*} : RegularExpression α → ZMod 2 → Prop
  | .zero, _ => True
  | .epsilon, p => p = 0
  | .char _, p => p = 1
  | .plus r s, p => regular_expression_typed_parity r p ∧ regular_expression_typed_parity s p
  | .comp r s, p => ∃ q₁ q₂ : ZMod 2, q₁ + q₂ = p ∧ regular_expression_typed_parity r q₁ ∧
      regular_expression_typed_parity s q₂
  | .star r, p => p = 0 ∧ regular_expression_typed_parity r 0
