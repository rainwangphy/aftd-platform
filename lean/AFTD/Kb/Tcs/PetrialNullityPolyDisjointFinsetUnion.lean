import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialNullityPoly
import AFTD.Kb.Tcs.PetrialNullityPolyMulOfCut
import AFTD.Kb.Tcs.PetrialNullityPolyInduceInduce
import AFTD.Kb.Tcs.PetrialNullityPolyIso

/-!
# petrial_nullity_poly_disjoint_finset_union

Topic: combinatorics   Node: fb79f6302660

Provenance: helper lemma. Component factorization for the OP-1239 candidate.

If disjoint finite vertex sets have no edges between them, the nullity polynomial on their union is the product of the nullity polynomials induced on the two sets.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem petrial_nullity_poly_disjoint_finset_union {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (s t : Finset V) (hdisj : Disjoint s t) (hcut : ∀ a ∈ s, ∀ b ∈ t, ¬ G.Adj a b) : petrial_nullity_poly (G.induce ((s ∪ t : Finset V) : Set V)) = petrial_nullity_poly (G.induce (s : Set V)) * petrial_nullity_poly (G.induce (t : Set V)) := by
  classical
  let S : Set V := ((s ∪ t : Finset V) : Set V)
  let A : Set S := {x | (x : V) ∈ s}
  have hc : ∀ a b : S, a ∈ A → b ∉ A → ¬ (G.induce S).Adj a b := by
    intro a b ha hb hadj
    have hbs : (b : V) ∉ s := hb
    have hbt : (b : V) ∈ t := by
      rcases Finset.mem_union.mp b.property with hs | ht
      · exact (hbs hs).elim
      · exact ht
    exact hcut a.1 ha b.1 hbt hadj
  let e1 : ((G.induce S).induce A) ≃g (G.induce (s : Set V)) := {
    toEquiv := {
      toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun x => ⟨⟨x.1, Finset.mem_union_left t x.2⟩, x.2⟩
      left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl
    }
    map_rel_iff' := by rfl
  }
  let e2 : ((G.induce S).induce Aᶜ) ≃g (G.induce (t : Set V)) := {
    toEquiv := {
      toFun := fun x => ⟨x.1.1, by
        have hn : (x.1 : V) ∉ s := x.2
        rcases Finset.mem_union.mp x.1.2 with hs | ht
        · exact (hn hs).elim
        · exact ht⟩
      invFun := fun x => ⟨⟨x.1, Finset.mem_union_right s x.2⟩, by
        change (x.1 : V) ∉ s
        intro hs
        exact (Finset.disjoint_left.mp hdisj) hs x.2⟩
      left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl
    }
    map_rel_iff' := by rfl
  }
  have h := petrial_nullity_poly_mul_of_cut (G.induce S) A hc
  rw [petrial_nullity_poly_iso _ _ e1, petrial_nullity_poly_iso _ _ e2] at h
  exact h
