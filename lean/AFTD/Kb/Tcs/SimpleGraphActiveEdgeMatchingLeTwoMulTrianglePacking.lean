import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.Vertices

/-!
# simple_graph_active_edge_matching_le_two_mul_triangle_packing

Topic: graphs   Node: 267710595114

Provenance: helper lemma. Matching-witness reduction for the sunflower-packing branch; no novelty claim.

In any finite simple graph, every vertex-disjoint matching of edges that each lie in a triangle has at most twice the triangle packing number.
-/

set_option maxHeartbeats 1000000 in
/-- If a triangle `Te` contains a two-element set `e` and another triangle `Tf` contains a two-element set `f` disjoint from `e`, and the two triangles share exactly two vertices, then the third vertex of `Te` lies in `f`. -/
private lemma simple_graph_active_edge_matching_le_two_mul_triangle_packing_aux_third_vertex
    {α : Type*} [DecidableEq α]
    {e Te f Tf : Finset α} (heTe : e ⊆ Te) (hec : e.card = 2) (hTc : Te.card = 3)
    (hfTf : f ⊆ Tf) (hfc : f.card = 2) (hTfc : Tf.card = 3) (hdis : Disjoint e f)
    (hint : (Te ∩ Tf).card = 2) : Te \ e ⊆ f := by
  intro z hz
  rw [Finset.mem_sdiff] at hz
  obtain ⟨hzTe, hze⟩ := hz
  have hTe : Te = insert z e := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hzTe
      · exact heTe hx
    · rw [Finset.card_insert_of_notMem hze, hec, hTc]
  have hzTf : z ∈ Tf := by
    by_contra hzTf
    have hsub : Te ∩ Tf ⊆ e := by
      intro x hx
      rw [Finset.mem_inter] at hx
      rw [hTe] at hx
      rcases Finset.mem_insert.1 hx.1 with rfl | hx1
      · exact absurd hx.2 hzTf
      · exact hx1
    have heq : Te ∩ Tf = e := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [hec, hint]
    have heTf : e ⊆ Tf := by
      intro x hx
      have : x ∈ Te ∩ Tf := by rw [heq]; exact hx
      exact (Finset.mem_inter.1 this).2
    have hunion : e ∪ f ⊆ Tf := fun x hx => by
      rcases Finset.mem_union.1 hx with hx | hx
      · exact heTf hx
      · exact hfTf hx
    have hle := Finset.card_le_card hunion
    rw [Finset.card_union_of_disjoint hdis, hec, hfc, hTfc] at hle
    omega
  by_contra hzf
  have hTf : Tf = insert z f := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hzTf
      · exact hfTf hx
    · rw [Finset.card_insert_of_notMem hzf, hfc, hTfc]
  have hsub : Te ∩ Tf ⊆ {z} := by
    intro x hx
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_singleton]
    by_contra hxz
    rw [hTe, hTf] at hx
    have hxe : x ∈ e := by
      rcases Finset.mem_insert.1 hx.1 with h | h
      · exact absurd h hxz
      · exact h
    have hxf : x ∈ f := by
      rcases Finset.mem_insert.1 hx.2 with h | h
      · exact absurd h hxz
      · exact h
    exact Finset.disjoint_left.1 hdis hxe hxf
  have hle := Finset.card_le_card hsub
  rw [Finset.card_singleton, hint] at hle
  omega

set_option maxHeartbeats 1000000 in
/-- Any family of triangles that pairwise share at most one vertex has at most `ν(G)` members. -/
private lemma simple_graph_active_edge_matching_le_two_mul_triangle_packing_aux_packing_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : Finset (Finset V))
    (hcl : ∀ t ∈ T, G.IsNClique 3 t)
    (hp : (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1)) :
    T.card ≤ simple_graph_triangle_packing_number G := by
  unfold simple_graph_triangle_packing_number
  have hbdd : BddAbove {n | ∃ T' : Finset (Finset V), (∀ t ∈ T', G.IsNClique 3 t) ∧
      (T' : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ T'.card = n} := by
    refine ⟨(Finset.univ : Finset (Finset V)).card, ?_⟩
    rintro n ⟨T', -, -, rfl⟩
    exact Finset.card_le_univ T'
  exact le_csSup hbdd ⟨T, hcl, hp, rfl⟩

theorem simple_graph_active_edge_matching_le_two_mul_triangle_packing (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Finset (Sym2 (Fin n))) (hactive : ∀ e ∈ M, e ∈ G.edgeSet ∧ ∃ t : Finset (Fin n), G.IsNClique 3 t ∧ e ∈ finite_vertex_set_edge_encoding t) (hmatching : (M : Set (Sym2 (Fin n))).Pairwise (fun e f => Disjoint e.toFinset f.toFinset)) : M.card ≤ 2 * simple_graph_triangle_packing_number G := by
  set_option maxHeartbeats 1000000 in
  classical
  have hex : ∀ e ∈ M, ∃ t : Finset (Fin n), G.IsNClique 3 t ∧
      e ∈ finite_vertex_set_edge_encoding t := fun e he => (hactive e he).2
  let t : Sym2 (Fin n) → Finset (Fin n) :=
    fun e => if h : e ∈ M then Classical.choose (hex e h) else ∅
  have ht : ∀ (e : Sym2 (Fin n)) (he : e ∈ M), G.IsNClique 3 (t e) ∧
      e ∈ finite_vertex_set_edge_encoding (t e) := by
    intro e he
    simp only [t, dif_pos he]
    exact Classical.choose_spec (hex e he)
  have htcl : ∀ e ∈ M, G.IsNClique 3 (t e) := fun e he => (ht e he).1
  have htcard : ∀ e ∈ M, (t e).card = 3 := fun e he => (htcl e he).card_eq
  have htmem : ∀ e ∈ M, e ∈ (t e).sym2 := fun e he => by
    have h3 := (ht e he).2
    rw [finite_vertex_set_edge_encoding, Finset.mem_filter] at h3
    exact h3.1
  have htndiag : ∀ e ∈ M, ¬ e.IsDiag := fun e he => by
    have h3 := (ht e he).2
    rw [finite_vertex_set_edge_encoding, Finset.mem_filter] at h3
    exact h3.2
  have htsub : ∀ e ∈ M, e.toFinset ⊆ t e := by
    intro e he x hx
    exact Finset.mem_sym2_iff.1 (htmem e he) x (Sym2.mem_toFinset.1 hx)
  have hcard2 : ∀ e ∈ M, e.toFinset.card = 2 := by
    intro e he
    rw [Sym2.card_toFinset, if_neg (htndiag e he)]
  have hdis : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e.toFinset f.toFinset :=
    fun e he f hf hne => hmatching he hf hne
  have hinj : ∀ e ∈ M, ∀ f ∈ M, t e = t f → e = f := by
    intro e he f hf hEq
    by_contra hne
    have hsub : e.toFinset ∪ f.toFinset ⊆ t f := by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · rw [← hEq]; exact htsub e he hx
      · exact htsub f hf hx
    have hle := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint (hdis e he f hf hne), hcard2 e he, hcard2 f hf,
      htcard f hf] at hle
    omega
  have hint2 : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → (t e ∩ t f).card ≤ 2 := by
    intro e he f hf hne
    have hle : (t e ∩ t f).card ≤ 3 := by
      have h := Finset.card_le_card (Finset.inter_subset_left : t e ∩ t f ⊆ t e)
      rwa [htcard e he] at h
    have hne3 : (t e ∩ t f).card ≠ 3 := by
      intro h3
      have heq : t e ∩ t f = t e := by
        apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
        rw [h3, htcard e he]
      have hsub : t e ⊆ t f := by rw [← heq]; exact Finset.inter_subset_right
      have hcard : (t f).card ≤ (t e).card := by rw [htcard e he, htcard f hf]
      exact hne (hinj e he f hf (Finset.eq_of_subset_of_card_le hsub hcard))
    omega
  have hkey : ∀ e ∈ M, ∀ f ∈ M, ∀ g ∈ M, e ≠ f → e ≠ g → f ≠ g →
      ¬ ((t e ∩ t f).card = 2 ∧ (t e ∩ t g).card = 2) := by
    intro e he f hf g hg hef heg hfg hcon
    obtain ⟨h1, h2⟩ := hcon
    have hsingle : (t e \ e.toFinset).card = 1 := by
      rw [Finset.card_sdiff]
      have h1' : e.toFinset ∩ t e = e.toFinset := Finset.inter_eq_left.2 (htsub e he)
      rw [h1', hcard2 e he, htcard e he]
    obtain ⟨z, hz⟩ := Finset.card_pos.1 (by rw [hsingle]; exact one_pos)
    have hzf : z ∈ f.toFinset :=
      (simple_graph_active_edge_matching_le_two_mul_triangle_packing_aux_third_vertex
        (htsub e he) (hcard2 e he) (htcard e he) (htsub f hf) (hcard2 f hf)
        (htcard f hf) (hdis e he f hf hef) h1) hz
    have hzg : z ∈ g.toFinset :=
      (simple_graph_active_edge_matching_le_two_mul_triangle_packing_aux_third_vertex
        (htsub e he) (hcard2 e he) (htcard e he) (htsub g hg) (hcard2 g hg)
        (htcard g hg) (hdis e he g hg heg) h2) hz
    exact Finset.disjoint_left.1 (hdis f hf g hg hfg) hzf hzg
  have hexmax : ∃ S : Finset (Sym2 (Fin n)),
      S ⊆ M ∧ (∀ e ∈ S, ∀ f ∈ S, e ≠ f → (t e ∩ t f).card ≤ 1) ∧
      ∀ S' : Finset (Sym2 (Fin n)), S' ⊆ M →
        (∀ e ∈ S', ∀ f ∈ S', e ≠ f → (t e ∩ t f).card ≤ 1) → S'.card ≤ S.card := by
    let A : Set ℕ := {k | ∃ S : Finset (Sym2 (Fin n)), S ⊆ M ∧
      (∀ e ∈ S, ∀ f ∈ S, e ≠ f → (t e ∩ t f).card ≤ 1) ∧ S.card = k}
    have hne : A.Nonempty := ⟨0, ∅, Finset.empty_subset _, by simp, rfl⟩
    have hbdd : BddAbove A := by
      refine ⟨M.card, ?_⟩
      rintro k ⟨S, hSM, -, rfl⟩
      exact Finset.card_le_card hSM
    have hsSup := Nat.sSup_mem hne hbdd
    obtain ⟨S, hSM, hSgood, hkS⟩ := hsSup
    refine ⟨S, hSM, hSgood, ?_⟩
    intro S' hS'M hS'good
    have hmem : S'.card ∈ A := ⟨S', hS'M, hS'good, rfl⟩
    rw [hkS]
    exact le_csSup hbdd hmem
  obtain ⟨S, hSM, hSgood, hSmax⟩ := hexmax
  have hcover : ∀ f ∈ M, f ∉ S → ∃ e ∈ S, (t e ∩ t f).card = 2 := by
    intro f hfM hfS
    have hex' : ∃ e ∈ S, 2 ≤ (t e ∩ t f).card := by
      by_contra hno
      push Not at hno
      have hinsM : insert f S ⊆ M := by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hfM
        · exact hSM hx
      have hinsgood : ∀ e ∈ insert f S, ∀ g ∈ insert f S, e ≠ g → (t e ∩ t g).card ≤ 1 := by
        intro e he g hg hne
        rcases Finset.mem_insert.1 he with rfl | heS'
        · rcases Finset.mem_insert.1 hg with hgf | hgS'
          · exact absurd hgf.symm hne
          · rw [Finset.inter_comm]
            have hlt := hno g hgS'
            omega
        · rcases Finset.mem_insert.1 hg with hgf | hgS'
          · subst hgf
            have hlt := hno e heS'
            omega
          · exact hSgood e heS' g hgS' hne
      have hres := hSmax (insert f S) hinsM hinsgood
      rw [Finset.card_insert_of_notMem hfS] at hres
      omega
    obtain ⟨e, heS, h2⟩ := hex'
    refine ⟨e, heS, le_antisymm (hint2 e (hSM heS) f hfM ?_) h2⟩
    intro h
    exact hfS (h ▸ heS)
  set R : Finset (Sym2 (Fin n)) := M \ S with hR
  have hRsub : R ⊆ M := fun x hx => (Finset.mem_sdiff.1 hx).1
  have hRnot : ∀ f ∈ R, f ∉ S := fun f hf => (Finset.mem_sdiff.1 hf).2
  have hexφ : ∀ f ∈ R, ∃ e, e ∈ S ∧ (t e ∩ t f).card = 2 :=
    fun f hf => hcover f (hRsub hf) (hRnot f hf)
  let φ : Sym2 (Fin n) → Sym2 (Fin n) :=
    fun f => if h : f ∈ R then Classical.choose (hexφ f h) else f
  have hφprop : ∀ (f : Sym2 (Fin n)) (hf : f ∈ R), φ f ∈ S ∧ (t (φ f) ∩ t f).card = 2 := by
    intro f hf
    simp only [φ, dif_pos hf]
    exact Classical.choose_spec (hexφ f hf)
  have hinjφ : ∀ f ∈ R, ∀ g ∈ R, φ f = φ g → f = g := by
    intro f hf g hg hEq
    by_contra hne
    have hfM := hRsub hf
    have hfS := hRnot f hf
    have hgM := hRsub hg
    have hgS := hRnot g hg
    have heS : φ f ∈ S := (hφprop f hf).1
    have heM : φ f ∈ M := hSM heS
    have hef : φ f ≠ f := fun h => hfS (h ▸ heS)
    have heg : φ f ≠ g := fun h => hgS (h ▸ heS)
    have h1 : (t (φ f) ∩ t f).card = 2 := (hφprop f hf).2
    have h2 : (t (φ g) ∩ t g).card = 2 := (hφprop g hg).2
    rw [← hEq] at h2
    exact hkey (φ f) heM f hfM g hgM hef heg hne ⟨h1, h2⟩
  have hRcard : R.card ≤ S.card := by
    refine Finset.card_le_card_of_injOn φ ?_ ?_
    · intro f hf
      exact (hφprop f hf).1
    · intro f hf g hg h
      exact hinjφ f hf g hg h
  have hSle : S.card ≤ simple_graph_triangle_packing_number G := by
    have hcl : ∀ x ∈ S.image t, G.IsNClique 3 x := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
      exact htcl e (hSM he)
    have hp : ((S.image t : Finset (Finset (Fin n))) : Set (Finset (Fin n))).Pairwise
        (fun s x => (s ∩ x).card ≤ 1) := by
      intro x hx y hy hne
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hy
      exact hSgood e he f hf (fun h => hne (by rw [h]))
    have hcard : (S.image t).card = S.card :=
      Finset.card_image_of_injOn (fun e he f hf h => hinj e (hSM he) f (hSM hf) h)
    rw [← hcard]
    exact simple_graph_active_edge_matching_le_two_mul_triangle_packing_aux_packing_card
      G (S.image t) hcl hp
  have hMcard : M.card = S.card + R.card := by
    have h := Finset.card_sdiff_add_card_eq_card hSM
    rw [← hR] at h
    omega
  calc M.card = S.card + R.card := hMcard
    _ ≤ S.card + S.card := by omega
    _ = 2 * S.card := by ring
    _ ≤ 2 * simple_graph_triangle_packing_number G := by omega
