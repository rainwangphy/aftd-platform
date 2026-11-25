import AFTD.Prelude
import AFTD.Kb.Tcs.EvenFoldDiag

/-!
# evenFoldDiag_length

Topic: combinatorics   Node: 5acce9b87698

Provenance: helper lemma. arXiv:2611.28952, Section 1.1, (3)

For any non-empty list d, the diagonal of the even fold of d with parameter δ has length 2 * |d|.
-/

/-- Length of the diagonal of an even fold. -/
theorem evenFoldDiag_length {R : Type*} [Sub R] [Add R] (d : List R) (δ : R) (h : d ≠ []) :
    (evenFoldDiag d δ).length = 2 * d.length := by
  unfold evenFoldDiag
  cases hr : d.reverse with
  | nil =>
    have : d = [] := by simpa using hr
    contradiction
  | cons dn drest =>
    have hd : d.length = drest.length + 1 := by
      have := congr_arg List.length hr
      simp only [List.length_reverse, List.length_cons] at this
      exact this
    simp only [List.length_append, List.length_cons, List.length_reverse]
    omega
