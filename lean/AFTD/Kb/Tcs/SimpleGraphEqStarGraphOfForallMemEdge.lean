import AFTD.Prelude

/-!
# simple_graph_eq_starGraph_of_forall_mem_edge

Topic: graphs   Node: 071bc16042a4

Provenance: helper lemma. Helper for arXiv:2610.12109 (Sharp linear Turán remainders for cycle and edge extremality), Lemma 2.5 (equality case of the upper bound: the extremal tree is a star).

A connected graph in which every edge contains the vertex r is the star centred at r.
-/

theorem simple_graph_eq_starGraph_of_forall_mem_edge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (r : V)
    (hr : ∀ e ∈ G.edgeSet, r ∈ e) : G = SimpleGraph.starGraph r := by
  ext a b
  rw [SimpleGraph.starGraph_adj]
  constructor
  · intro h
    refine ⟨G.ne_of_adj h, ?_⟩
    have := hr s(a, b) h
    rw [Sym2.mem_iff] at this
    rcases this with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr h'.symm
  · rintro ⟨hab, hab'⟩
    -- the endpoint different from r has a neighbour, which must be r
    have key : ∀ c, c ≠ r → G.Adj c r := by
      intro c hc
      obtain ⟨p⟩ := hconn.preconnected c r
      cases p with
      | nil => exact absurd rfl hc
      | @cons _ d _ h _ =>
        have := hr s(c, d) h
        rw [Sym2.mem_iff] at this
        rcases this with h' | h'
        · exact absurd h'.symm hc
        · exact h' ▸ h
    rcases hab' with rfl | rfl
    · exact (key b (Ne.symm hab)).symm
    · exact key a hab
