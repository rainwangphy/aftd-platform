import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsChoosable

/-!
# simple_graph_choice_number

Topic: graphs   Node: af577651fb3c

Provenance: formalization of a published result. Source: arXiv:2611.03151, Section 1; Erdős, Rubin, Taylor (1979)

The choice number (or list chromatic number) ch(G) of a simple graph G is the infimum over all natural numbers k such that G is k-choosable, as an element of ℕ∞.
-/

/-- The choice number (list chromatic number) of a simple graph as an extended natural number. -/
noncomputable def simple_graph_choice_number {V : Type*} (G : SimpleGraph V) : ℕ∞ := ⨅ k ∈ {n : ℕ | simple_graph_is_choosable G n}, (k : ℕ∞)
