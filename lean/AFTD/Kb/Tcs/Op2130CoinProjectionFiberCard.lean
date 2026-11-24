import AFTD.Prelude

/-!
# op2130_coin_projection_fiber_card

Topic: online_algorithms   Node: a63faa1cf47c

Provenance: helper lemma. OP-2130, uniform fair-coin projection

Each assignment to m distinct coin positions extends to exactly 2^(T-m) Boolean tapes of length T.
-/

theorem op2130_coin_projection_fiber_card (T m : ℕ) (hm : m ≤ T) (idx : Fin m → Fin T) (hinj : Function.Injective idx) (a : Fin m → Bool) : (by classical exact (Finset.univ.filter (fun r : Fin T → Bool => ∀ j, r (idx j) = a j)).card = 2^(T-m)) := by
  classical
  let P : (Fin T → Bool) → Prop := fun r => ∀ j, r (idx j) = a j
  let C := {i : Fin T // ¬ ∃ j, idx j = i}
  let e : {r : Fin T → Bool // P r} ≃ (C → Bool) := {
    toFun := fun r i => r.val i.val
    invFun := fun b => ⟨fun i => if h : ∃ j, idx j = i then a (Classical.choose h) else b ⟨i,h⟩, by
      intro j
      simp only [dif_pos (show ∃ k, idx k = idx j from ⟨j,rfl⟩)]
      congr 1
      apply hinj
      exact Classical.choose_spec (show ∃ k, idx k = idx j from ⟨j,rfl⟩)⟩
    left_inv := by
      intro r
      apply Subtype.ext
      funext i
      dsimp only
      by_cases h : ∃ j, idx j = i
      · simp only [dif_pos h]
        calc
          a (Classical.choose h) = r.val (idx (Classical.choose h)) :=
            (r.property (Classical.choose h)).symm
          _ = r.val i := congrArg r.val (Classical.choose_spec h)
      · simp only [dif_neg h]
    right_inv := by
      intro b
      funext i
      dsimp only
      simp only [dif_neg i.property]
      apply congrArg b
      exact Subtype.ext rfl }
  have hC : Fintype.card C = T-m := by
    dsimp only [C]
    have hr : Fintype.card {i : Fin T // ∃ j, idx j = i} = m := by
      have he : Fintype.card (Fin m) = Fintype.card {i : Fin T // ∃ j, idx j = i} :=
        Fintype.card_congr (Equiv.ofInjective idx hinj)
      rw [Fintype.card_fin] at he
      exact he.symm
    rw [Fintype.card_subtype_compl, hr, Fintype.card_fin]
  change (Finset.univ.filter P).card = _
  have hc : (Finset.univ.filter P).card = Fintype.card {r : Fin T → Bool // P r} := by
    symm
    rw [Fintype.card_subtype]
  rw [hc, Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool, hC]
