import AFTD.Prelude

/-!
# eval_binary_word

Topic: automata   Node: f6d3cf2f403e

Provenance: formalization of a published result. Source: arXiv:2610.11098 Section 1

The evaluation of a binary word `w : List (Fin 2)` on elements `σ₀, σ₁` of a monoid `G` is the product in `G` of the letters mapped by `0 ↦ σ₀` and `1 ↦ σ₁`.
-/

/-- Evaluates a binary word (as a list over `Fin 2`) on a pair of elements `σ₀, σ₁` of a monoid `G`. -/
def eval_binary_word {G : Type*} [Monoid G] (w : List (Fin 2)) (σ₀ σ₁ : G) : G := (w.map (![σ₀, σ₁])).prod
