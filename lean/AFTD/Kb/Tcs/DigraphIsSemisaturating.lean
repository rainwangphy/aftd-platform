import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsOriented

/-!
# digraph_is_semisaturating

Topic: graphs   Node: e92e140d42c9

Provenance: formalization of a published result. Source: arXiv:2610.18600 Definition 1.2

A host digraph H : Digraph W on vertex type W semisaturates a digraph G : Digraph V on vertex type V (digraph_is_semisaturating H G) if digraph_is_oriented H holds, and for any two distinct vertices x y : W with ¬ H.Adj x y and ¬ H.Adj y x, there exists an injective function f : V → W such that for all a b : V, G.Adj a b implies H.Adj (f a) (f b) ∨ (f a = x ∧ f b = y), and there exist a b : V with G.Adj a b and f a = x ∧ f b = y.
-/

/-- A host digraph H semisaturates G if H is oriented and adding any non-edge creates a copy of G using that edge. -/
def digraph_is_semisaturating {V W : Type*} (H : Digraph W) (G : Digraph V) : Prop := digraph_is_oriented H ∧ ∀ x y : W, x ≠ y → ¬ H.Adj x y → ¬ H.Adj y x → ∃ f : V → W, Function.Injective f ∧ (∀ a b, G.Adj a b → (H.Adj (f a) (f b) ∨ (f a = x ∧ f b = y))) ∧ (∃ a b, G.Adj a b ∧ f a = x ∧ f b = y)
