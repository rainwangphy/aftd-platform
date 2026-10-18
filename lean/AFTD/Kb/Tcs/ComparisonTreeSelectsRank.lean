import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTree
import AFTD.Kb.Tcs.ComparisonTreeEval

/-!
# comparison_tree_selects_rank

Topic: algorithms   Node: 46ed46b6f622

Provenance: formalization of a published result. Source: scout/2610-18740-selecting-the-7th-smallest-of-16-elements-takes-exactly-28.md:Sec. 3

A comparison decision tree T on n elements (T : ComparisonTree n) correctly selects the element of rank r : Fin n if for every permutation σ : Equiv.Perm (Fin n), applying σ to the index returned by evaluating T on σ equals r, that is, σ (comparison_tree_eval σ T) = r.
-/

/-- A comparison decision tree on n elements selects rank r if on every permutation of Fin n it returns the index whose value is r. -/
def comparison_tree_selects_rank {n : ℕ} (T : ComparisonTree n) (r : Fin n) : Prop := ∀ σ : Equiv.Perm (Fin n), σ (comparison_tree_eval σ T) = r
