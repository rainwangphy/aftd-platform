import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumberEqZeroOfCliqueFree

/-!
# simple_graph_triangle_cover_number_mono

Topic: graphs   Node: 1638b342a30f

Provenance: helper lemma. step towards simple_graph_triangle_cover_number_le_two_mul_packing_number

Triangle cover number is monotone under subgraph inclusion: if H ≤ G, then τ(H) ≤ τ(G).
-/

/-- Triangle cover number is monotone under subgraph inclusion: if H ≤ G, then τ(H) ≤ τ(G). -/
theorem simple_graph_triangle_cover_number_mono {V : Type*} [Fintype V]
    (G H : SimpleGraph V) (hle : H ≤ G) :
    simple_graph_triangle_cover_number H ≤ simple_graph_triangle_cover_number G := by
  classical
  have hne : {n | ∃ F : Finset (Sym2 V), (∀ e ∈ F, e ∈ G.edgeSet) ∧
      (∀ t : Finset V, G.IsNClique 3 t → ∃ e ∈ F, ∀ x ∈ e, x ∈ t) ∧ F.card = n}.Nonempty := by
    refine ⟨_, Finset.univ.filter (· ∈ G.edgeSet), ?_, ?_, rfl⟩
    · intro e he
      rw [Finset.mem_filter] at he
      exact he.2
    · intro t ht
      obtain ⟨x, y, z, hxy, -, -, rfl⟩ := Finset.card_eq_three.1 ht.card_eq
      have hadj : G.Adj x y := ht.isClique (by simp) (by simp) hxy
      refine ⟨s(x, y), ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hadj⟩
      · intro v hv
        simp only [Sym2.mem_iff] at hv
        rcases hv with rfl | rfl <;> simp
  obtain ⟨F, hFedge, hFcover, hFcard⟩ := Nat.sInf_mem hne
  change F.card = simple_graph_triangle_cover_number G at hFcard
  set F' : Finset (Sym2 V) := F.filter (· ∈ H.edgeSet)
  have hF'edge : ∀ e ∈ F', e ∈ H.edgeSet := by
    intro e he
    rw [Finset.mem_filter] at he
    exact he.2
  have hF'cover : ∀ t : Finset V, H.IsNClique 3 t → ∃ e ∈ F', ∀ x ∈ e, x ∈ t := by
    intro t ht
    obtain ⟨e, heF, het⟩ := hFcover t (ht.mono hle)
    induction' e using Sym2.ind with u v
    have heG : G.Adj u v := hFedge s(u, v) heF
    have hne : u ≠ v := G.ne_of_adj heG
    have hu : u ∈ t := het u (by simp)
    have hv : v ∈ t := het v (by simp)
    have hadj : H.Adj u v := ht.isClique hu hv hne
    refine ⟨s(u, v), ?_, het⟩
    rw [Finset.mem_filter]
    exact ⟨heF, hadj⟩
  have hHle : simple_graph_triangle_cover_number H ≤ F'.card := by
    apply Nat.sInf_le
    exact ⟨F', hF'edge, hF'cover, rfl⟩
  rw [← hFcard]
  exact hHle.trans (Finset.card_filter_le _ _)
