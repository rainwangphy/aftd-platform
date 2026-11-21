import AFTD.Prelude
import AFTD.Kb.Tcs.GraphIsDImmune
import AFTD.Kb.Tcs.GraphHasDCut
import AFTD.Kb.Tcs.GraphIsDCut

/-!
# top_is_d_immune

Topic: graphs   Node: 7149185beab9

Provenance: formalization of a published result. Source: arXiv:2611.26556 Section 1

For any d and any finite vertex set of size at least 2d + 1, the complete simple graph is d-immune.
-/

/-- In the complete graph, the neighbour finset of any vertex is the complement of
the singleton, for any choice of the finiteness instance on the neighbour set. -/
lemma top_is_d_immune_neighborFinset_top_at {V : Type*} [Fintype V] [DecidableEq V] (u : V)
    (i : Fintype ↑((⊤ : SimpleGraph V).neighborSet u)) :
    @SimpleGraph.neighborFinset V (⊤ : SimpleGraph V) u i = {u}ᶜ := by
  unfold SimpleGraph.neighborFinset
  ext x
  rw [@Set.mem_toFinset _ _ i, Finset.mem_compl, Finset.mem_singleton]
  simp [SimpleGraph.neighborSet, SimpleGraph.top_adj, eq_comm]

/-- The complete graph on at least 2d + 1 vertices is d-immune. -/
lemma top_is_d_immune {V : Type*} [Fintype V] [DecidableEq V]
    (d : ℕ) (hV : 2 * d + 1 ≤ Fintype.card V) :
    graph_is_d_immune (⊤ : SimpleGraph V) d := by
  rw [graph_is_d_immune, graph_has_d_cut]
  rintro ⟨A, hne, hcne, h1, h2⟩
  obtain ⟨u, hu⟩ := hne
  obtain ⟨v, hv⟩ := hcne
  have hvA : v ∉ A := by simpa using hv
  have hAcard : Aᶜ.card ≤ d := by
    have h := h1 u hu
    rw [top_is_d_immune_neighborFinset_top_at] at h
    have hEq : ({u}ᶜ : Finset V) \ A = Aᶜ := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hx⟩; exact hx
      · intro hx; exact ⟨fun hux => hx (hux ▸ hu), hx⟩
    rwa [hEq] at h
  have hAcard2 : A.card ≤ d := by
    have h := h2 v hv
    rw [top_is_d_immune_neighborFinset_top_at] at h
    have hEq : ({v}ᶜ : Finset V) ∩ A = A := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hx⟩; exact hx
      · intro hx; exact ⟨fun hvx => hvA (hvx ▸ hx), hx⟩
    rwa [hEq] at h
  have htot : A.card + Aᶜ.card = Fintype.card V := Finset.card_add_card_compl A
  omega
