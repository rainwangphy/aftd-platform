import AFTD.Prelude
import AFTD.Kb.Tcs.IsStrongOddColoring

/-!
# is_strong_odd_list_colorable

Topic: graphs   Node: 8179542d6e85

Provenance: original. Related work: arXiv:2610.34874

A finite simple graph G is strongly odd k-list-colorable if for every assignment L of color lists of size at least k to the vertices from any palette κ, G admits a strong odd coloring f with f(v) ∈ L(v) for all v.
-/

/-- A finite simple graph G is strongly odd k-list-colorable. -/
def is_strong_odd_list_colorable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop := ∀ (κ : Type) [DecidableEq κ] (L : V → Finset κ) (_ : ∀ v, k ≤ (L v).card),
    ∃ f : V → κ, (∀ v, f v ∈ L v) ∧ is_strong_odd_coloring G f
