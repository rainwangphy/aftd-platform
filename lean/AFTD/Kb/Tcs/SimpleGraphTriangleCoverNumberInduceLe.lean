import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber

/-!
# simple_graph_triangle_cover_number_induce_le

Topic: graphs   Node: 2536c523ae12

Provenance: helper lemma. step towards simple_graph_triangle_packing_cover_bounded_induced_kernel

The triangle cover number of an induced subgraph does not exceed that of the host graph.
-/

theorem simple_graph_triangle_cover_number_induce_le
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    simple_graph_triangle_cover_number (G.induce (S : Set V)) ≤
      simple_graph_triangle_cover_number G := by
  classical
  have hne : {n | ∃ F : Finset (Sym2 V), (∀ e ∈ F, e ∈ G.edgeSet) ∧
      (∀ t : Finset V, G.IsNClique 3 t → ∃ e ∈ F, ∀ x ∈ e, x ∈ t) ∧ F.card = n}.Nonempty := by
    refine ⟨_, Finset.univ.filter (· ∈ G.edgeSet), ?_, ?_, rfl⟩
    · intro e he
      exact (Finset.mem_filter.mp he).2
    · intro t ht
      obtain ⟨x, y, z, hxy, -, -, rfl⟩ := Finset.card_eq_three.1 ht.card_eq
      have hadj : G.Adj x y := ht.isClique (by simp) (by simp) hxy
      refine ⟨s(x, y), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
      · intro v hv
        simp only [Sym2.mem_iff] at hv
        rcases hv with rfl | rfl <;> simp
  obtain ⟨F, hFedge, hFcover, hFcard⟩ := Nat.sInf_mem hne
  change F.card = simple_graph_triangle_cover_number G at hFcard
  let emb : S ↪ V := Function.Embedding.subtype (fun x => x ∈ S)
  let edgeEmb : Sym2 S ↪ Sym2 V := emb.sym2Map
  let F' : Finset (Sym2 S) := Finset.univ.filter fun e =>
    e ∈ (G.induce (S : Set V)).edgeSet ∧ edgeEmb e ∈ F
  have hF'edge : ∀ e ∈ F', e ∈ (G.induce (S : Set V)).edgeSet := by
    intro e he
    exact (Finset.mem_filter.mp he).2.1
  have hF'cover : ∀ t : Finset S, (G.induce (S : Set V)).IsNClique 3 t →
      ∃ e ∈ F', ∀ x ∈ e, x ∈ t := by
    intro t ht
    have htG : G.IsNClique 3 (t.map emb) := by
      exact (G.isNClique_induce_iff (S : Set V) t 3).mp ht
    obtain ⟨e, heF, het⟩ := hFcover (t.map emb) htG
    induction e using Sym2.ind with
    | _ u v =>
      have hu : u ∈ t.map emb := het u (by simp)
      have hv : v ∈ t.map emb := het v (by simp)
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
      have hab : a ≠ b := by
        intro h
        subst b
        have : G.Adj (emb a) (emb a) := hFedge _ heF
        exact (G.ne_of_adj this) rfl
      have hadj : (G.induce (S : Set V)).Adj a b := ht.isClique ha hb hab
      refine ⟨s(a,b), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, hadj, ?_⟩
        simpa [edgeEmb, emb] using heF
      · intro x hx
        simp only [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl <;> assumption
  have hcard : F'.card ≤ F.card := by
    calc
      F'.card = (F'.map edgeEmb).card := (Finset.card_map _).symm
      _ ≤ F.card := by
        apply Finset.card_le_card
        intro e he
        obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp he
        exact (Finset.mem_filter.mp hx).2.2
  have hle : simple_graph_triangle_cover_number (G.induce (S : Set V)) ≤ F'.card := by
    apply Nat.sInf_le
    exact ⟨F', hF'edge, hF'cover, rfl⟩
  rw [← hFcard]
  exact hle.trans hcard
