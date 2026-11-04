import AFTD.Prelude

/-!
# matrix_cut_norm

Topic: graphs   Node: 7a0643eacf9a

Provenance: formalization of a published result. Source: arXiv:2611.05048 Section 1; Frieze-Kannan 1999

The cut norm of a real matrix M indexed by finite sets α and β is the maximum over all subsets S ⊆ α and T ⊆ β of the absolute value of the sum of M(i, j) for i ∈ S and j ∈ T.
-/

/-- The cut norm of a real matrix indexed by finite types α and β. -/
def matrix_cut_norm {α β : Type*} [Fintype α] [Fintype β] (M : α → β → ℝ) : ℝ := (Finset.univ : Finset (Finset α × Finset β)).sup' Finset.univ_nonempty
    (fun (S, T) => |∑ i ∈ S, ∑ j ∈ T, M i j|)
