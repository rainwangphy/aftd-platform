import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTree
import AFTD.Kb.Tcs.ComparisonTreeEval
import AFTD.Kb.Tcs.IsLinearExtension

/-!
# comparison_tree_correct_for_selection

Topic: algorithms   Node: 113fef7ce7ae

Provenance: formalization of a published result. Source: arXiv:2610.18740 Section 5

Given a natural number n, a partial order P on Fin n, a rank i, and a comparison tree t on n elements, t correctly selects the i-th smallest element for P if for every linear extension L of P on Fin n, evaluating t under L yields an element of Fin n with exactly i - 1 elements strictly smaller than it under L.
-/

/-- A comparison tree on Fin n correctly selects the i-th smallest element under all linear extensions. -/
def comparison_tree_correct_for_selection (n : ℕ) (P : PartialOrder (Fin n)) (i : ℕ) (t : ComparisonTree n) : Prop := open scoped Classical in
  ∀ (L : LinearOrder (Fin n)), is_linear_extension P L →
    letI := L
    (Finset.filter (fun x => x < comparison_tree_eval (fun a => a) t) Finset.univ).card = i - 1
