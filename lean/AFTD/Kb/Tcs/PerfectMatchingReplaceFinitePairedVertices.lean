import AFTD.Prelude

/-!
# perfect_matching_replace_finite_paired_vertices

Topic: graphs   Node: fefebfa79063

Provenance: helper lemma. OP-1957: reusable kernel-checked construction for four- and six-vertex alternating switches; adapt the finite-pairing construction in minimally_k_extendable_order_two_mul_add_six_min_degree_le.

Given a perfect matching P and a subgraph M of it, if a finite injective list of vertices is paired internally by P, avoids M, and admits a new graph-edge pairing represented by an involution, replacing the old list pairs by the new ones yields a perfect matching still containing M.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

theorem perfect_matching_replace_finite_paired_vertices
    {V : Type*} (G : SimpleGraph V) (P M : G.Subgraph)
    (hP : P.IsPerfectMatching) (hMP : M ≤ P)
    (m : ℕ) (f : Fin m → V) (hf : Function.Injective f)
    (τ σ : Fin m → Fin m) (hτ : ∀ i, P.Adj (f i) (f (τ i)))
    (hσ : ∀ i, σ (σ i) = i) (hnew : ∀ i, G.Adj (f i) (f (σ i)))
    (hdisj : ∀ i, f i ∉ M.verts) :
    ∃ Q : G.Subgraph, Q.IsPerfectMatching ∧ M ≤ Q ∧ ∀ i, Q.Adj (f i) (f (σ i)) := by
  classical
  have hP' := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP
  have hmate : ∀ {a b c : V}, P.Adj a b → P.Adj a c → b = c :=
    fun {a b c} h1 h2 => (hP' a).unique h1 h2
  have hTclos : ∀ i (w : V), P.Adj (f i) w → w ∈ Set.range f :=
    fun i w h => ⟨τ i, hmate (hτ i) h⟩
  refine ⟨⟨Set.univ, fun x y =>
    (P.Adj x y ∧ x ∉ Set.range f ∧ y ∉ Set.range f) ∨
      ∃ i, x = f i ∧ y = f (σ i), ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rintro x y (⟨h, -, -⟩ | ⟨i, rfl, rfl⟩)
    · exact P.adj_sub h
    · exact hnew i
  · intro x y _
    exact Set.mem_univ x
  · refine ⟨fun x y hxy => ?_⟩
    rcases hxy with ⟨h,hx,hy⟩ | ⟨i,rfl,rfl⟩
    · exact Or.inl ⟨h.symm,hy,hx⟩
    · exact Or.inr ⟨σ i,rfl,by rw [hσ i]⟩
  · rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
    intro x
    by_cases hx : x ∈ Set.range f
    · obtain ⟨i,rfl⟩ := hx
      refine ⟨f (σ i), Or.inr ⟨i,rfl,rfl⟩, ?_⟩
      rintro w (⟨-,hx,-⟩ | ⟨j,hj,rfl⟩)
      · exact absurd ⟨i,rfl⟩ hx
      · rw [hf hj]
    · obtain ⟨w,hw,huniq⟩ := hP' x
      have hwT : w ∉ Set.range f := by
        rintro ⟨i,rfl⟩
        exact hx (hTclos i x hw.symm)
      refine ⟨w, Or.inl ⟨hw,hx,hwT⟩, ?_⟩
      rintro w' (⟨h',-,-⟩ | ⟨j,hj,-⟩)
      · exact huniq w' h'
      · exact absurd ⟨j,hj.symm⟩ hx
  · refine ⟨fun x _ => Set.mem_univ x, fun x y h => Or.inl ⟨hMP.2 h, ?_, ?_⟩⟩
    · rintro ⟨i,rfl⟩
      exact hdisj i (M.edge_vert h)
    · rintro ⟨i,rfl⟩
      exact hdisj i (M.edge_vert h.symm)
  · intro i
    exact Or.inr ⟨i,rfl,rfl⟩
