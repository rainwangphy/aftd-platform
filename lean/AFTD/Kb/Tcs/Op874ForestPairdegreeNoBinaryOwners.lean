import AFTD.Prelude

/-!
# op874_forest_pairdegree_no_binary_owners

Topic: graphs   Node: c450bbb399d2

Provenance: helper lemma. OP-874: forest and pair-degree fixed-color obstruction, experiments 38456 and 38468.

The explicit sixteen-vertex missing-color data have no conflict-free binary assignment of each shared-color edge demand to one endpoint.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
private def op874f16L : Fin 24 → Fin 16 := ![0,0,0,1,1,1,2,2,2,3,3,3,4,5,5,6,6,7,8,9,10,11,12,14]
private def op874f16R : Fin 24 → Fin 16 := ![5,6,7,4,12,15,4,10,13,8,10,11,7,13,14,8,14,9,9,12,11,15,13,15]
private def op874f16Missing : Fin 16 → Finset (Fin 6) := ![{2,4,5},{0,2,5},{0,1,2},{0,1,4},{0,3,4},{0,2,3},{1,4,5},{0,1,5},{1,2,4},{1,3,5},{0,2,5},{3,4,5},{1,4,5},{1,2,4},{0,1,3},{1,2,3}]
private def op874f16Shared (e : Fin 24) (z : Fin 6) : Prop :=
  z ∈ op874f16Missing (op874f16L e) ∧ z ∈ op874f16Missing (op874f16R e)
private instance (e : Fin 24) (z : Fin 6) : Decidable (op874f16Shared e z) := by
  unfold op874f16Shared
  infer_instance

theorem op874_forest_pairdegree_no_binary_owners :
    let L : Fin 24 → Fin 16 := ![0,0,0,1,1,1,2,2,2,3,3,3,4,5,5,6,6,7,8,9,10,11,12,14]
    let R : Fin 24 → Fin 16 := ![5,6,7,4,12,15,4,10,13,8,10,11,7,13,14,8,14,9,9,12,11,15,13,15]
    let missing : Fin 16 → Finset (Fin 6) := ![{2,4,5},{0,2,5},{0,1,2},{0,1,4},{0,3,4},{0,2,3},{1,4,5},{0,1,5},{1,2,4},{1,3,5},{0,2,5},{3,4,5},{1,4,5},{1,2,4},{0,1,3},{1,2,3}]
    ¬ ∃ q : Fin 24 → Fin 6 → Fin 16,
      (∀ e z, (z ∈ missing (L e) ∧ z ∈ missing (R e)) → q e z = L e ∨ q e z = R e) ∧
      (∀ e f a b, (a ∈ missing (L e) ∧ a ∈ missing (R e)) →
        (b ∈ missing (L f) ∧ b ∈ missing (R f)) → q e a = q f b → (e=f ↔ a=b)) := by
  change ¬ ∃ q : Fin 24 → Fin 6 → Fin 16,
      (∀ e z, op874f16Shared e z → q e z = op874f16L e ∨ q e z = op874f16R e) ∧
      (∀ e f a b, op874f16Shared e a → op874f16Shared f b → q e a = q f b → (e=f ↔ a=b))
  rintro ⟨q,hends,hcollision⟩
  have step (e f : Fin 24) (a b : Fin 6) (v w : Fin 16)
      (hv : q e a = v) (he : op874f16Shared e a) (hf : op874f16Shared f b)
      (hend : (op874f16L f=v ∧ op874f16R f=w) ∨
        (op874f16L f=w ∧ op874f16R f=v))
      (hconf : (e=f ∧ a≠b) ∨ (e≠f ∧ a=b)) : q f b = w := by
    have hbad : q f b ≠ v := by
      intro hv'
      have h := hcollision e f a b he hf (hv.trans hv'.symm)
      rcases hconf with ⟨hef,hab⟩ | ⟨hef,hab⟩
      · exact hab (h.mp hef)
      · exact hef (h.mpr hab)
    rcases hend with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · rcases hends f b hf with hleft | hright
      · exact (hbad (hleft.trans hl)).elim
      · exact hright.trans hr
    · rcases hends f b hf with hleft | hright
      · exact hleft.trans hl
      · exact (hbad (hright.trans hr)).elim
  have hor := hends 15 1 (by decide)
  rcases hor with h0 | h0
  ·
    have h1 : q 15 4 = 8 := step 15 15 1 4 6 8 h0 (by decide) (by decide) (by decide) (by decide)
    have h2 : q 9 4 = 3 := step 15 9 4 4 8 3 h1 (by decide) (by decide) (by decide) (by decide)
    have h3 : q 9 1 = 8 := step 9 9 4 1 3 8 h2 (by decide) (by decide) (by decide) (by decide)
    have h4 : q 18 1 = 9 := step 9 18 1 1 8 9 h3 (by decide) (by decide) (by decide) (by decide)
    have h5 : q 19 1 = 12 := step 18 19 1 1 9 12 h4 (by decide) (by decide) (by decide) (by decide)
    have h6 : q 19 5 = 9 := step 19 19 1 5 12 9 h5 (by decide) (by decide) (by decide) (by decide)
    have h7 : q 17 5 = 7 := step 19 17 5 5 9 7 h6 (by decide) (by decide) (by decide) (by decide)
    have h8 : q 17 1 = 9 := step 17 17 5 1 7 9 h7 (by decide) (by decide) (by decide) (by decide)
    have h9 : q 18 1 = 8 := step 17 18 1 1 9 8 h8 (by decide) (by decide) (by decide) (by decide)
    have h10 : q 9 1 = 3 := step 18 9 1 1 8 3 h9 (by decide) (by decide) (by decide) (by decide)
    have h11 : q 9 4 = 8 := step 9 9 1 4 3 8 h10 (by decide) (by decide) (by decide) (by decide)
    have h12 : q 15 4 = 6 := step 9 15 4 4 8 6 h11 (by decide) (by decide) (by decide) (by decide)
    have h13 : q 15 1 = 8 := step 15 15 4 1 6 8 h12 (by decide) (by decide) (by decide) (by decide)
    exact (by decide : (6 : Fin 16) ≠ 8) (h0.symm.trans h13)
  ·
    have h1 : q 18 1 = 9 := step 15 18 1 1 8 9 h0 (by decide) (by decide) (by decide) (by decide)
    have h2 : q 17 1 = 7 := step 18 17 1 1 9 7 h1 (by decide) (by decide) (by decide) (by decide)
    have h3 : q 17 5 = 9 := step 17 17 1 5 7 9 h2 (by decide) (by decide) (by decide) (by decide)
    have h4 : q 19 5 = 12 := step 17 19 5 5 9 12 h3 (by decide) (by decide) (by decide) (by decide)
    have h5 : q 19 1 = 9 := step 19 19 5 1 12 9 h4 (by decide) (by decide) (by decide) (by decide)
    have h6 : q 18 1 = 8 := step 19 18 1 1 9 8 h5 (by decide) (by decide) (by decide) (by decide)
    have h7 : q 15 1 = 6 := step 18 15 1 1 8 6 h6 (by decide) (by decide) (by decide) (by decide)
    exact (by decide : (8 : Fin 16) ≠ 6) (h0.symm.trans h7)
