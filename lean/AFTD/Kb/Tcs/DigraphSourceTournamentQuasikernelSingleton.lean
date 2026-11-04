import AFTD.Prelude

/-!
# digraph_source_tournament_quasikernel_singleton

Topic: graphs   Node: b80c18f5b1a2

Provenance: helper lemma. Elementary block lemma for the explicit counterexample in experiment 14471; no novelty is claimed.

If a nonempty tournament vertex set sends every arc to its complement and receives none, then every quasi-kernel of the whole digraph is a singleton in that tournament.
-/

theorem digraph_source_tournament_quasikernel_singleton
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (S Q : Finset α) (hS : S.Nonempty)
    (htour : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → D.Adj u v ∨ D.Adj v u)
    (hcross : ∀ u ∈ S, ∀ v, v ∉ S → D.Adj u v ∧ ¬ D.Adj v u)
    (hind : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v)
    (hreach : ∀ v, ∃ q ∈ Q, q = v ∨ D.Adj q v ∨ ∃ z, D.Adj q z ∧ D.Adj z v) :
    ∃ s ∈ S, Q = {s} := by
  classical
  -- A quasi-kernel must meet `S`: no vertex outside `S` can reach `S`, not even in two steps.
  have hmeet : ∃ s ∈ S, s ∈ Q := by
    obtain ⟨s₀, hs₀⟩ := hS
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    obtain ⟨q, hqQ, hcase⟩ := hreach s₀
    have hqS : q ∉ S := fun h => hcon q h hqQ
    rcases hcase with h | h | ⟨z, hqz, hzs⟩
    · exact hqS (h ▸ hs₀)
    · exact (hcross s₀ hs₀ q hqS).2 h
    · by_cases hz : z ∈ S
      · exact (hcross z hz q hqS).2 hqz
      · exact (hcross s₀ hs₀ z hz).2 hzs
  -- Once one member of `S` lies in `Q`, the complete cross-arcs force `Q ⊆ S`.
  have hQS : Q ⊆ S := by
    intro q hq
    by_contra hqS
    obtain ⟨s₀, hs₀, hs₀Q⟩ := hmeet
    have hne : s₀ ≠ q := fun h => hqS (h ▸ hs₀)
    exact hind s₀ hs₀Q q hq hne (hcross s₀ hs₀ q hqS).1
  -- Independence inside the tournament `S` leaves at most one vertex.
  obtain ⟨s₀, hs₀, hs₀Q⟩ := hmeet
  refine ⟨s₀, hs₀, ?_⟩
  have hsub : Q ⊆ {s₀} := by
    intro q hq
    simp only [Finset.mem_singleton]
    by_contra hne
    have h1 : s₀ ≠ q := fun h => hne h.symm
    rcases htour s₀ hs₀ q (hQS hq) h1 with h | h
    · exact hind s₀ hs₀Q q hq h1 h
    · exact hind q hq s₀ hs₀Q hne h
  exact Finset.Subset.antisymm hsub
    (by intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ hs₀Q)
