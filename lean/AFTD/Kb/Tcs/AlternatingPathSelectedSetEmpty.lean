import AFTD.Prelude
import AFTD.Kb.Tcs.AlternatingPathSelectedSet
import AFTD.Kb.Tcs.SimpleGraphIsDominatingUniv

/-!
# alternating_path_selected_set_empty

Topic: graphs   Node: 363e67c7f7eb

Provenance: helper lemma. arXiv:2611.06985 Section 3.2

For a simple graph C on vertex type V, a vertex ρ : V, and a subset A of the subtype {ρ}ᶜ, alternating_path_selected_set C ρ A ∅ = A.
-/

/-- When T is empty, the alternating path selected set equals A. -/
theorem alternating_path_selected_set_empty {V : Type*} (C : SimpleGraph V) (ρ : V)
    (A : Set ({ρ}ᶜ : Set V)) :
    alternating_path_selected_set C ρ A ∅ = A := by first | exact simple_graph_is_dominating_univ | (apply simple_graph_is_dominating_univ <;> assumption) | (apply simple_graph_is_dominating_univ <;> simp_all) | simpa using simple_graph_is_dominating_univ | (simp only [alternating_path_selected_set] at *; first | exact simple_graph_is_dominating_univ | (apply simple_graph_is_dominating_univ <;> assumption) | (apply simple_graph_is_dominating_univ <;> simp_all) | simpa using simple_graph_is_dominating_univ)
