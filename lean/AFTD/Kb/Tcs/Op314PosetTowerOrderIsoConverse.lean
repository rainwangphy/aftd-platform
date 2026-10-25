import AFTD.Prelude
import AFTD.Kb.Tcs.PosetTower

/-!
# op314_poset_tower_order_iso_converse

Topic: combinatorics   Node: cd112f25efed

Provenance: helper lemma. arXiv:2610.20802 Sec. 5

For any natural number k and any types α and β equipped with partial orders [PartialOrder α] and [PartialOrder β], if there exists an order-isomorphism α ≃o β, then there exists an order-isomorphism poset_tower α k ≃o poset_tower β k between their height-k right-associated exponentiation towers.
-/

private def op314_poset_tower_order_iso_converse_arrowFun {P Q A B : Type*} [PartialOrder P]
    [PartialOrder Q] [PartialOrder A] [PartialOrder B] (eP : P ≃o Q) (eA : A ≃o B)
    (f : P →o A) : Q →o B :=
  OrderHom.mk (fun q => eA (f (eP.symm q)))
    (by intro a b hq; exact eA.monotone (f.monotone (eP.symm.monotone hq)))

private lemma op314_poset_tower_order_iso_converse_arrowFun_apply {P Q A B : Type*}
    [PartialOrder P] [PartialOrder Q] [PartialOrder A] [PartialOrder B]
    (eP : P ≃o Q) (eA : A ≃o B) (f : P →o A) (q : Q) :
    op314_poset_tower_order_iso_converse_arrowFun eP eA f q = eA (f (eP.symm q)) := rfl

private def op314_poset_tower_order_iso_converse_arrowInv {P Q A B : Type*} [PartialOrder P]
    [PartialOrder Q] [PartialOrder A] [PartialOrder B] (eP : P ≃o Q) (eA : A ≃o B)
    (g : Q →o B) : P →o A :=
  OrderHom.mk (fun p => eA.symm (g (eP p)))
    (by intro a b hp; exact eA.symm.monotone (g.monotone (eP.monotone hp)))

private lemma op314_poset_tower_order_iso_converse_arrowInv_apply {P Q A B : Type*}
    [PartialOrder P] [PartialOrder Q] [PartialOrder A] [PartialOrder B]
    (eP : P ≃o Q) (eA : A ≃o B) (g : Q →o B) (p : P) :
    op314_poset_tower_order_iso_converse_arrowInv eP eA g p = eA.symm (g (eP p)) := rfl

private lemma op314_poset_tower_order_iso_converse_left_inv {P Q A B : Type*} [PartialOrder P]
    [PartialOrder Q] [PartialOrder A] [PartialOrder B] (eP : P ≃o Q) (eA : A ≃o B)
    (f : P →o A) :
    op314_poset_tower_order_iso_converse_arrowInv eP eA
      (op314_poset_tower_order_iso_converse_arrowFun eP eA f) = f := by
  ext p
  rw [op314_poset_tower_order_iso_converse_arrowInv_apply,
    op314_poset_tower_order_iso_converse_arrowFun_apply, eP.symm_apply_apply,
    eA.symm_apply_apply]

private lemma op314_poset_tower_order_iso_converse_right_inv {P Q A B : Type*} [PartialOrder P]
    [PartialOrder Q] [PartialOrder A] [PartialOrder B] (eP : P ≃o Q) (eA : A ≃o B)
    (g : Q →o B) :
    op314_poset_tower_order_iso_converse_arrowFun eP eA
      (op314_poset_tower_order_iso_converse_arrowInv eP eA g) = g := by
  ext q
  rw [op314_poset_tower_order_iso_converse_arrowFun_apply,
    op314_poset_tower_order_iso_converse_arrowInv_apply, eP.apply_symm_apply,
    eA.apply_symm_apply]

private lemma op314_poset_tower_order_iso_converse_map_rel {P Q A B : Type*} [PartialOrder P]
    [PartialOrder Q] [PartialOrder A] [PartialOrder B] (eP : P ≃o Q) (eA : A ≃o B)
    {f g : P →o A} :
    op314_poset_tower_order_iso_converse_arrowFun eP eA f ≤
      op314_poset_tower_order_iso_converse_arrowFun eP eA g ↔ f ≤ g := by
  rw [OrderHom.le_def, OrderHom.le_def]
  constructor
  · intro h p
    have h' := h (eP p)
    simp only [op314_poset_tower_order_iso_converse_arrowFun_apply,
      eP.symm_apply_apply] at h'
    exact (eA.le_iff_le).1 h'
  · intro h q
    rw [op314_poset_tower_order_iso_converse_arrowFun_apply]
    exact eA.monotone (h (eP.symm q))

private def op314_poset_tower_order_iso_converse_arrowOrderIso {P Q A B : Type*} [PartialOrder P]
    [PartialOrder Q] [PartialOrder A] [PartialOrder B] (eP : P ≃o Q) (eA : A ≃o B) :
    (P →o A) ≃o (Q →o B) :=
  RelIso.mk
    { toFun := op314_poset_tower_order_iso_converse_arrowFun eP eA
      invFun := op314_poset_tower_order_iso_converse_arrowInv eP eA
      left_inv := op314_poset_tower_order_iso_converse_left_inv eP eA
      right_inv := op314_poset_tower_order_iso_converse_right_inv eP eA }
    (op314_poset_tower_order_iso_converse_map_rel eP eA)

/-- Order-isomorphic posets have order-isomorphic right-associated exponentiation towers at any height k. -/
theorem op314_poset_tower_order_iso_converse (k : ℕ) (α β : Type*) [PartialOrder α] [PartialOrder β] (h : Nonempty (α ≃o β)) : Nonempty (poset_tower α k ≃o poset_tower β k) := by
  induction k using poset_tower.induct with
  | case1 =>
      rw [poset_tower.eq_1 α, poset_tower.eq_1 β]
      change Nonempty (α ≃o β)
      exact h
  | case2 =>
      rw [poset_tower.eq_2 α, poset_tower.eq_2 β]
      change Nonempty (α ≃o β)
      exact h
  | case3 k hk ih =>
      obtain ⟨eP⟩ := ih
      obtain ⟨eA⟩ := h
      rw [poset_tower.eq_3 α k hk, poset_tower.eq_3 β k hk]
      exact ⟨op314_poset_tower_order_iso_converse_arrowOrderIso eP eA⟩
