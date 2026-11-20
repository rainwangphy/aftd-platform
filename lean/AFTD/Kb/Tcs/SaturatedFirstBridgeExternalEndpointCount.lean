import AFTD.Prelude
import AFTD.Kb.Tcs.BoundedDegreeDisjointNeighborUnion

/-!
# saturated_first_bridge_external_endpoint_count

Topic: graphs   Node: db8a4aa50a56

Provenance: helper lemma. OP-1957 uniform saturated-first-bridge counting reduction.

Two endpoints of a saturated first bridge cover at most |A|+|B| external neighbors, without any restriction on shore sizes.
-/

theorem saturated_first_bridge_external_endpoint_count {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (d : ℕ)
    (x y u v : V) (hxy : x ≠ y) (A B C : Finset V)
    (hAB : Disjoint A B) (hu : u ∈ A) (hv : v ∈ B)
    (hx : x ∉ A ∪ B) (hy : y ∉ A ∪ B) (hxC : x ∉ C) (hyC : y ∉ C)
    (hCS : Disjoint C (A ∪ B)) (hsize : A.card + B.card + 1 = d)
    (hxyA : ∀ a ∈ A ∪ B, H.Adj a x ∧ H.Adj a y)
    (hcut : ∀ a ∈ A, ∀ b ∈ B, (a ≠ u ∨ b ≠ v) → H.Adj a b)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (hcover : ∀ c ∈ C, H.Adj u c ∨ H.Adj v c) : C.card ≤ A.card + B.card := by
  classical
  let C₁ := C.filter (H.Adj u)
  let C₂ := C.filter (fun c => ¬ H.Adj u c)
  have hc₁ : C₁ ⊆ C := Finset.filter_subset _ _
  have hc₂ : C₂ ⊆ C := Finset.filter_subset _ _
  have hSxA : x ∉ A := fun h => hx (Finset.mem_union_left B h)
  have hSyA : y ∉ A := fun h => hy (Finset.mem_union_left B h)
  have hSxB : x ∉ B := fun h => hx (Finset.mem_union_right A h)
  have hSyB : y ∉ B := fun h => hy (Finset.mem_union_right A h)
  have hc₁dis : Disjoint (B.erase v) C₁ := by
    apply Finset.disjoint_left.mpr
    intro a ha hc
    exact (Finset.disjoint_left.mp hCS) (hc₁ hc)
      (Finset.mem_union_right A (Finset.mem_of_mem_erase ha))
  have hc₂dis : Disjoint (A.erase u) C₂ := by
    apply Finset.disjoint_left.mpr
    intro a ha hc
    exact (Finset.disjoint_left.mp hCS) (hc₂ hc)
      (Finset.mem_union_left B (Finset.mem_of_mem_erase ha))
  have h1 := bounded_degree_disjoint_neighbor_union H u x y (B.erase v) C₁ hxy
    (fun h => hSxB (Finset.mem_of_mem_erase h)) (fun h => hSyB (Finset.mem_of_mem_erase h))
    (fun h => hxC (hc₁ h)) (fun h => hyC (hc₁ h)) hc₁dis
    (hxyA u (Finset.mem_union_left B hu)).1 (hxyA u (Finset.mem_union_left B hu)).2
    (by intro a ha; exact hcut u hu a (Finset.mem_of_mem_erase ha) (Or.inr (Finset.ne_of_mem_erase ha)))
    (by intro a ha; exact (Finset.mem_filter.mp ha).2) d (hmax u)
  have h2 := bounded_degree_disjoint_neighbor_union H v x y (A.erase u) C₂ hxy
    (fun h => hSxA (Finset.mem_of_mem_erase h)) (fun h => hSyA (Finset.mem_of_mem_erase h))
    (fun h => hxC (hc₂ h)) (fun h => hyC (hc₂ h)) hc₂dis
    (hxyA v (Finset.mem_union_right A hv)).1 (hxyA v (Finset.mem_union_right A hv)).2
    (by intro a ha; exact (hcut a (Finset.mem_of_mem_erase ha) v hv (Or.inl (Finset.ne_of_mem_erase ha))).symm)
    (by intro a ha; exact (hcover a (hc₂ ha)).resolve_left ((Finset.mem_filter.mp ha).2)) d (hmax v)
  rw [Finset.card_erase_of_mem hv] at h1
  rw [Finset.card_erase_of_mem hu] at h2
  have hsum : C₁.card + C₂.card = C.card := by
    simpa [C₁,C₂] using Finset.card_filter_add_card_filter_not (s := C) (p := H.Adj u)
  have hA : 0 < A.card := Finset.card_pos.mpr ⟨u,hu⟩
  have hB : 0 < B.card := Finset.card_pos.mpr ⟨v,hv⟩
  omega
