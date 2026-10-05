import AFTD.Prelude

/-!
# gpa_indep

Topic: mechanism_design   Node: e437bd12461d

An independent set of the graph G.
-/

open Finset in
/-- An independent set of the graph `G`. -/
def gpa_indep {k : ℕ} (G : SimpleGraph (Fin k)) (S : Finset (Fin k)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ¬ G.Adj i j
