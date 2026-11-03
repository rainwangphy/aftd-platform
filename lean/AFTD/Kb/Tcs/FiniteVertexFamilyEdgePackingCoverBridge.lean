import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding
import AFTD.Kb.Tcs.F

/-!
# finite_vertex_family_edge_packing_cover_bridge

Topic: graphs   Node: 369817cc5ef3

Provenance: helper lemma. Bridge for the published separator reduction, https://www.cs.tau.ac.il/~krivelev/2.pdf, Lemma 5.

Encoding each member of a finite vertex-set family of size at least two by its non-diagonal pairs preserves the family size, converts vertex-intersection-at-most-one packings into disjoint set packings, and converts nondiagnonal edge covers into point covers.
-/

private theorem in519_mk_mem_edges {V : Type*} [DecidableEq V] (s : Finset V) (a b : V) :
    s(a,b) ∈ finite_vertex_set_edge_encoding s ↔ a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  simp [finite_vertex_set_edge_encoding, Sym2.mk_isDiag_iff, and_assoc]

private theorem in519_edges_disjoint_iff_inter_small {V : Type*} [DecidableEq V] (s t : Finset V) :
    Disjoint (finite_vertex_set_edge_encoding s) (finite_vertex_set_edge_encoding t) ↔ (s ∩ t).card ≤ 1 := by
  constructor
  · intro h
    by_contra hn
    have hgt : 1 < (s ∩ t).card := by omega
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hgt
    have ha' := Finset.mem_inter.mp ha
    have hb' := Finset.mem_inter.mp hb
    have he₁ : s(a,b) ∈ finite_vertex_set_edge_encoding s := (in519_mk_mem_edges s a b).mpr ⟨ha'.1,hb'.1,hab⟩
    have he₂ : s(a,b) ∈ finite_vertex_set_edge_encoding t := (in519_mk_mem_edges t a b).mpr ⟨ha'.2,hb'.2,hab⟩
    exact Finset.disjoint_left.mp h he₁ he₂
  · intro h
    apply Finset.disjoint_left.mpr
    intro e he₁ he₂
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha,hb,hab⟩ := (in519_mk_mem_edges s a b).mp he₁
      obtain ⟨ha',hb',_⟩ := (in519_mk_mem_edges t a b).mp he₂
      have hgt : 1 < (s ∩ t).card := Finset.one_lt_card.mpr
        ⟨a,Finset.mem_inter.mpr ⟨ha,ha'⟩,b,Finset.mem_inter.mpr ⟨hb,hb'⟩,hab⟩
      omega

private theorem in519_edges_injective_on_nontrivial {V : Type*} [DecidableEq V] (s t : Finset V)
    (hs : 2 ≤ s.card) (ht : 2 ≤ t.card)
    (heq : finite_vertex_set_edge_encoding s = finite_vertex_set_edge_encoding t) : s = t := by
  have hex : ∀ (r : Finset V), 2 ≤ r.card → ∀ x ∈ r, ∃ y ∈ r, x ≠ y := by
    intro r hr x hx
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega : 1 < r.card)
    by_cases h : x = a
    · exact ⟨b,hb,by simpa [h] using hab⟩
    · exact ⟨a,ha,h⟩
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y,hy,hxy⟩ := hex s hs x hx
    have he : s(x,y) ∈ finite_vertex_set_edge_encoding t := by
      rw [← heq]
      exact (in519_mk_mem_edges s x y).mpr ⟨hx,hy,hxy⟩
    exact ((in519_mk_mem_edges t x y).mp he).1
  · intro hx
    obtain ⟨y,hy,hxy⟩ := hex t ht x hx
    have he : s(x,y) ∈ finite_vertex_set_edge_encoding s := by
      rw [heq]
      exact (in519_mk_mem_edges t x y).mpr ⟨hx,hy,hxy⟩
    exact ((in519_mk_mem_edges s x y).mp he).1


private theorem in519_edge_image_card {V : Type*} [DecidableEq V]
    (P : Finset (Finset V)) (hsize : ∀ t ∈ P, 2 ≤ t.card) :
    (P.image finite_vertex_set_edge_encoding).card = P.card := by
  apply Finset.card_image_iff.mpr
  intro s hs t ht heq
  exact in519_edges_injective_on_nontrivial s t (hsize s hs) (hsize t ht) heq

private theorem in519_edge_image_packing_iff {V : Type*} [DecidableEq V]
    (P : Finset (Finset V)) (hsize : ∀ t ∈ P, 2 ≤ t.card) :
    ((P.image finite_vertex_set_edge_encoding : Finset (Finset (Sym2 V))) :
      Set (Finset (Sym2 V))).Pairwise Disjoint ↔
      (P : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) := by
  constructor
  · intro h s hs t ht hne
    have hne' : finite_vertex_set_edge_encoding s ≠ finite_vertex_set_edge_encoding t := by
      intro heq
      exact hne (in519_edges_injective_on_nontrivial s t (hsize s hs) (hsize t ht) heq)
    apply (in519_edges_disjoint_iff_inter_small s t).mp
    exact h (Finset.mem_image.mpr ⟨s,hs,rfl⟩) (Finset.mem_image.mpr ⟨t,ht,rfl⟩) hne'
  · intro h s hs t ht hne
    obtain ⟨s',hs',rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨t',ht',rfl⟩ := Finset.mem_image.mp ht
    have hne' : s' ≠ t' := by intro heq; exact hne (congrArg finite_vertex_set_edge_encoding heq)
    exact (in519_edges_disjoint_iff_inter_small s' t').mpr (h hs' ht' hne')


private theorem in519_edge_image_cover_iff {V : Type*} [DecidableEq V]
    (P : Finset (Finset V)) (C : Finset (Sym2 V))
    (hC : ∀ e ∈ C, ¬ e.IsDiag) :
    (∀ F ∈ P.image finite_vertex_set_edge_encoding, ¬ Disjoint F C) ↔
      (∀ t ∈ P, ∃ e ∈ C, ∀ x ∈ e, x ∈ t) := by
  constructor
  · intro h t ht
    have ht' : finite_vertex_set_edge_encoding t ∈ P.image finite_vertex_set_edge_encoding :=
      Finset.mem_image.mpr ⟨t,ht,rfl⟩
    obtain ⟨e,he,hC⟩ := Finset.not_disjoint_iff.mp (h _ ht')
    refine ⟨e,hC,?_⟩
    exact Finset.mem_sym2_iff.mp (Finset.mem_filter.mp he).1
  · intro h F hF
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨e,he,hsub⟩ := h t ht
    apply Finset.not_disjoint_iff.mpr
    refine ⟨e,?_,he⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_sym2_iff.mpr hsub,hC e he⟩

theorem finite_vertex_family_edge_packing_cover_bridge {V : Type*} [DecidableEq V]
    (P : Finset (Finset V)) (C : Finset (Sym2 V))
    (hsize : ∀ t ∈ P, 2 ≤ t.card) (hC : ∀ e ∈ C, ¬ e.IsDiag) :
    (P.image finite_vertex_set_edge_encoding).card = P.card ∧
    (((P.image finite_vertex_set_edge_encoding : Finset (Finset (Sym2 V))) :
        Set (Finset (Sym2 V))).Pairwise Disjoint ↔
      (P : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1)) ∧
    ((∀ F ∈ P.image finite_vertex_set_edge_encoding, ¬ Disjoint F C) ↔
      (∀ t ∈ P, ∃ e ∈ C, ∀ x ∈ e, x ∈ t)) := by
  exact ⟨in519_edge_image_card P hsize, in519_edge_image_packing_iff P hsize, in519_edge_image_cover_iff P C hC⟩
