import AFTD.Prelude

/-!
# op874_two_four_forest_no_binary_owners

Topic: graphs   Node: 68695c46eeec

Provenance: helper lemma. OP-874: two-versus-four forest and pair-degree obstruction, experiments 38473 and 38476.

The explicit 16-vertex two-versus-four missing-color data have no conflict-free binary assignment of all shared-color edge demands to endpoints.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
private def op874f16L : Fin 24 → Fin 16 := ![0,0,0,1,1,2,2,3,3,4,4,5,6,6,6,7,8,9,10,11,11,12,13,14]
private def op874f16R : Fin 24 → Fin 16 := ![1,5,14,2,9,3,12,4,13,5,15,7,7,8,10,8,9,10,11,12,15,13,14,15]
private def op874f16Missing : Fin 16 → Finset (Fin 6) := ![{0,3,5},{1,3,5},{0,3,5},{1,2,3},{0,2,4},{1,4,5},{0,4,5},{1,3,4},{0,2,3},{1,2,3},{1,2,4},{1,2,3},{0,3,4},{1,4,5},{0,2,4},{0,2,3}]
private def op874f16Shared (e : Fin 24) (z : Fin 6) : Prop :=
  z ∈ op874f16Missing (op874f16L e) ∧ z ∈ op874f16Missing (op874f16R e)
private instance (e : Fin 24) (z : Fin 6) : Decidable (op874f16Shared e z) := by
  unfold op874f16Shared
  infer_instance

theorem op874_two_four_forest_no_binary_owners :
    let L : Fin 24 → Fin 16 := ![0,0,0,1,1,2,2,3,3,4,4,5,6,6,6,7,8,9,10,11,11,12,13,14]
    let R : Fin 24 → Fin 16 := ![1,5,14,2,9,3,12,4,13,5,15,7,7,8,10,8,9,10,11,12,15,13,14,15]
    let missing : Fin 16 → Finset (Fin 6) := ![{0,3,5},{1,3,5},{0,3,5},{1,2,3},{0,2,4},{1,4,5},{0,4,5},{1,3,4},{0,2,3},{1,2,3},{1,2,4},{1,2,3},{0,3,4},{1,4,5},{0,2,4},{0,2,3}]
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
  have hor := hends 0 3 (by decide)
  rcases hor with h0 | h0
  ·
    have h1 : q 0 5 = 1 := step 0 0 3 5 0 1 h0 (by decide) (by decide) (by decide) (by decide)
    have h2 : q 3 5 = 2 := step 0 3 5 5 1 2 h1 (by decide) (by decide) (by decide) (by decide)
    have h3 : q 3 3 = 1 := step 3 3 5 3 2 1 h2 (by decide) (by decide) (by decide) (by decide)
    have h4 : q 4 3 = 9 := step 3 4 3 3 1 9 h3 (by decide) (by decide) (by decide) (by decide)
    have h5 : q 16 3 = 8 := step 4 16 3 3 9 8 h4 (by decide) (by decide) (by decide) (by decide)
    have h6 : q 16 2 = 9 := step 16 16 3 2 8 9 h5 (by decide) (by decide) (by decide) (by decide)
    have h7 : q 17 2 = 10 := step 16 17 2 2 9 10 h6 (by decide) (by decide) (by decide) (by decide)
    have h8 : q 18 2 = 11 := step 17 18 2 2 10 11 h7 (by decide) (by decide) (by decide) (by decide)
    have h9 : q 20 2 = 15 := step 18 20 2 2 11 15 h8 (by decide) (by decide) (by decide) (by decide)
    have h10 : q 23 2 = 14 := step 20 23 2 2 15 14 h9 (by decide) (by decide) (by decide) (by decide)
    have h11 : q 23 0 = 15 := step 23 23 2 0 14 15 h10 (by decide) (by decide) (by decide) (by decide)
    have h12 : q 10 0 = 4 := step 23 10 0 0 15 4 h11 (by decide) (by decide) (by decide) (by decide)
    have h13 : q 10 2 = 15 := step 10 10 0 2 4 15 h12 (by decide) (by decide) (by decide) (by decide)
    have h14 : q 20 2 = 11 := step 10 20 2 2 15 11 h13 (by decide) (by decide) (by decide) (by decide)
    have h15 : q 18 2 = 10 := step 20 18 2 2 11 10 h14 (by decide) (by decide) (by decide) (by decide)
    have h16 : q 17 2 = 9 := step 18 17 2 2 10 9 h15 (by decide) (by decide) (by decide) (by decide)
    have h17 : q 16 2 = 8 := step 17 16 2 2 9 8 h16 (by decide) (by decide) (by decide) (by decide)
    have h18 : q 16 3 = 9 := step 16 16 2 3 8 9 h17 (by decide) (by decide) (by decide) (by decide)
    have h19 : q 4 3 = 1 := step 16 4 3 3 9 1 h18 (by decide) (by decide) (by decide) (by decide)
    have h20 : q 3 3 = 2 := step 4 3 3 3 1 2 h19 (by decide) (by decide) (by decide) (by decide)
    have h21 : q 3 5 = 1 := step 3 3 3 5 2 1 h20 (by decide) (by decide) (by decide) (by decide)
    have h22 : q 0 5 = 0 := step 3 0 5 5 1 0 h21 (by decide) (by decide) (by decide) (by decide)
    have h23 : q 0 3 = 1 := step 0 0 5 3 0 1 h22 (by decide) (by decide) (by decide) (by decide)
    exact (by decide : (0 : Fin 16) ≠ 1) (h0.symm.trans h23)
  ·
    have h1 : q 3 3 = 2 := step 0 3 3 3 1 2 h0 (by decide) (by decide) (by decide) (by decide)
    have h2 : q 6 3 = 12 := step 3 6 3 3 2 12 h1 (by decide) (by decide) (by decide) (by decide)
    have h3 : q 19 3 = 11 := step 6 19 3 3 12 11 h2 (by decide) (by decide) (by decide) (by decide)
    have h4 : q 20 3 = 15 := step 19 20 3 3 11 15 h3 (by decide) (by decide) (by decide) (by decide)
    have h5 : q 20 2 = 11 := step 20 20 3 2 15 11 h4 (by decide) (by decide) (by decide) (by decide)
    have h6 : q 18 2 = 10 := step 20 18 2 2 11 10 h5 (by decide) (by decide) (by decide) (by decide)
    have h7 : q 17 2 = 9 := step 18 17 2 2 10 9 h6 (by decide) (by decide) (by decide) (by decide)
    have h8 : q 16 2 = 8 := step 17 16 2 2 9 8 h7 (by decide) (by decide) (by decide) (by decide)
    have h9 : q 16 3 = 9 := step 16 16 2 3 8 9 h8 (by decide) (by decide) (by decide) (by decide)
    have h10 : q 4 3 = 1 := step 16 4 3 3 9 1 h9 (by decide) (by decide) (by decide) (by decide)
    have h11 : q 0 3 = 0 := step 4 0 3 3 1 0 h10 (by decide) (by decide) (by decide) (by decide)
    exact (by decide : (1 : Fin 16) ≠ 0) (h0.symm.trans h11)
