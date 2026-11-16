import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialNullityPoly
import AFTD.Kb.Tcs.PetrialNullityPolyLeafRec
import AFTD.Kb.Tcs.PetrialNullityPolyInduceInduce
import AFTD.Kb.Tcs.PetrialNullityPolyIso

/-!
# petrial_nullity_poly_leaf_finset

Topic: combinatorics   Node: 41ec424ad63a

Provenance: helper lemma. Leaf-deletion certificate for the OP-1239 candidate.

If v is a leaf with neighbor u in the subgraph induced by the finite set s, its nullity polynomial is that after deleting v plus twice that after deleting v and u.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem petrial_nullity_poly_leaf_finset {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (v u : V) (hv : v ∈ s) (hu : u ∈ s) (hdeg : (G.induce (s : Set V)).degree ⟨v, hv⟩ = 1) (hedge : G.Adj v u) : petrial_nullity_poly (G.induce (s : Set V)) = petrial_nullity_poly (G.induce ((s.erase v : Finset V) : Set V)) + 2 * petrial_nullity_poly (G.induce (((s.erase v).erase u : Finset V) : Set V)) := by
  classical
  let S : Set V := (s : Set V)
  let vv : S := ⟨v, hv⟩
  let uu : S := ⟨u, hu⟩
  let e1 : ((G.induce S).induce ({vv}ᶜ : Set S)) ≃g
      G.induce ((s.erase v : Finset V) : Set V) := {
    toEquiv := {
      toFun := fun x => ⟨x.1.1, by
        apply Finset.mem_erase.mpr
        refine ⟨?_, x.1.2⟩
        intro h
        have hsub : x.1 = vv := Subtype.ext h
        exact x.2 (by simpa [hsub])⟩
      invFun := fun x => ⟨⟨x.1, (Finset.mem_erase.mp x.2).2⟩, by
        change (⟨x.1, (Finset.mem_erase.mp x.2).2⟩ : S) ∉ ({vv} : Set S)
        simp only [Set.mem_singleton_iff]
        intro h
        exact (Finset.mem_erase.mp x.2).1 (congrArg Subtype.val h)⟩
      left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl
    }
    map_rel_iff' := by rfl
  }
  let e2 : ((G.induce S).induce (({uu} ∪ {vv})ᶜ : Set S)) ≃g
      G.induce (((s.erase v).erase u : Finset V) : Set V) := {
    toEquiv := {
      toFun := fun x => ⟨x.1.1, by
        apply Finset.mem_erase.mpr
        constructor
        · intro h
          have hsub : x.1 = uu := Subtype.ext h
          exact x.2 (by simp [hsub])
        · apply Finset.mem_erase.mpr
          constructor
          · intro h
            have hsub : x.1 = vv := Subtype.ext h
            exact x.2 (by simp [hsub])
          · exact x.1.2⟩
      invFun := fun x => ⟨⟨x.1, (Finset.mem_erase.mp (Finset.mem_erase.mp x.2).2).2⟩, by
        change (⟨x.1, (Finset.mem_erase.mp (Finset.mem_erase.mp x.2).2).2⟩ : S) ∉ ({uu} ∪ {vv} : Set S)
        simp only [Set.mem_union, Set.mem_singleton_iff, not_or]
        constructor
        · intro h
          exact (Finset.mem_erase.mp x.2).1 (congrArg Subtype.val h)
        · intro h
          exact (Finset.mem_erase.mp (Finset.mem_erase.mp x.2).2).1 (congrArg Subtype.val h)⟩
      left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl
    }
    map_rel_iff' := by rfl
  }
  have hadj : (G.induce S).Adj vv uu := hedge
  have h := petrial_nullity_poly_leaf_rec (G.induce S) hdeg hadj
  rw [petrial_nullity_poly_iso _ _ e1, petrial_nullity_poly_iso _ _ e2] at h
  exact h
