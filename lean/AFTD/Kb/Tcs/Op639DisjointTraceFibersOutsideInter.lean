import AFTD.Prelude

/-!
# op_639_disjoint_trace_fibers_outside_inter

Topic: combinatorics   Node: 66c8365b9eb4

Provenance: helper lemma. step towards op_639_intersecting_four_uniform_covering_four_card_le_forty_two

Let F be an intersecting family and T any set. If e1, e2 in F have disjoint intersections with T, then their differences e1 \ T and e2 \ T must not be disjoint.
-/

/-- For any two edges in an intersecting hypergraph having disjoint traces on T, their outside traces e1 \ T and e2 \ T must intersect. -/
theorem op_639_disjoint_trace_fibers_outside_inter
    {V : Type*} [DecidableEq V] (F : Finset (Finset V))
    (hinter : (F : Set (Finset V)).Intersecting)
    (T : Finset V)
    (e1 e2 : Finset V) (he1 : e1 ∈ F) (he2 : e2 ∈ F)
    (hdisj : Disjoint (e1 ∩ T) (e2 ∩ T)) :
    ¬Disjoint (e1 \ T) (e2 \ T) := by
  have hne : ¬Disjoint e1 e2 := hinter he1 he2
  rw [Finset.not_disjoint_iff] at hne ⊢
  rcases hne with ⟨x, hx1, hx2⟩
  by_cases hxT : x ∈ T
  · exfalso
    have h1 : x ∈ e1 ∩ T := Finset.mem_inter.mpr ⟨hx1, hxT⟩
    have h2 : x ∈ e2 ∩ T := Finset.mem_inter.mpr ⟨hx2, hxT⟩
    exact Finset.disjoint_left.mp hdisj h1 h2
  · refine ⟨x, Finset.mem_sdiff.mpr ⟨hx1, hxT⟩, Finset.mem_sdiff.mpr ⟨hx2, hxT⟩⟩
