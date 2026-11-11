import AFTD.Prelude

/-!
# ZeroForced

Topic: graphs   Node: 7df0f7d4c755

Provenance: formalization of a published result. Source: arXiv:2611.11352 Section 1

The zero forcing closure of an initial set S of blue vertices in G under the color change rule.
-/

/-- Inductive definition of vertices in the zero forcing closure of S. -/
inductive ZeroForced {V : Type*} (G : SimpleGraph V) (S : Set V) : V → Prop | init (v : V) : v ∈ S → ZeroForced G S v
  | step (u : V) (w : V) : ZeroForced G S u → G.Adj u w →
      (∀ x, G.Adj u x → x ≠ w → ZeroForced G S x) → ZeroForced G S w
