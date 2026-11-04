import AFTD.Prelude

/-!
# digraph_delete_dominated_vertex_quasikernel_lift

Topic: graphs   Node: c376a0308702

Provenance: helper lemma. Proof of Theorem 3.4, step (1), in https://people.maths.ox.ac.uk/~scott/Papers/2kernels.pdf; only the kernel of the non-neighborhood is used, and no novelty is claimed.

If a vertex w points to v and every in-neighbor of w also points to v, then every quasi-kernel after deleting v remains a quasi-kernel when v is restored; direct coverage of w also covers v.
-/

theorem digraph_delete_dominated_vertex_quasikernel_lift
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (v w : α) (hne : w ≠ v)
    (hwv : D.Adj w v) (hin : ∀ z, D.Adj z w → D.Adj z v)
    (Q : Finset α) (hnot : v ∉ Q)
    (hind : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → ¬ D.Adj x y)
    (hsub : ∀ x, x ≠ v → ∃ q ∈ Q,
      q = x ∨ D.Adj q x ∨ ∃ z, z ≠ v ∧ D.Adj q z ∧ D.Adj z x) :
    (∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → ¬ D.Adj x y) ∧
    (∀ x, ∃ q ∈ Q, q = x ∨ D.Adj q x ∨ ∃ z, D.Adj q z ∧ D.Adj z x) ∧
    ((∃ q ∈ Q, q = w ∨ D.Adj q w) → ∃ q ∈ Q, q = v ∨ D.Adj q v) := by
  refine ⟨hind, ?_, ?_⟩
  · intro x
    by_cases hx : x = v
    · subst x
      obtain ⟨q, hq, h⟩ := hsub w hne
      rcases h with h | h | ⟨z, _, hqz, hzw⟩
      · subst q
        exact ⟨w, hq, Or.inr (Or.inl hwv)⟩
      · exact ⟨q, hq, Or.inr (Or.inl (hin q h))⟩
      · exact ⟨q, hq, Or.inr (Or.inr ⟨z, hqz, hin z hzw⟩)⟩
    · obtain ⟨q, hq, h⟩ := hsub x hx
      rcases h with h | h | ⟨z, _, hqz, hzx⟩
      · exact ⟨q, hq, Or.inl h⟩
      · exact ⟨q, hq, Or.inr (Or.inl h)⟩
      · exact ⟨q, hq, Or.inr (Or.inr ⟨z, hqz, hzx⟩)⟩
  · rintro ⟨q, hq, h | h⟩
    · subst q
      exact ⟨w, hq, Or.inr hwv⟩
    · exact ⟨q, hq, Or.inr (hin q h)⟩
