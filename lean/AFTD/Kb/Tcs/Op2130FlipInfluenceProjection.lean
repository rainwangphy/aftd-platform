import AFTD.Prelude

/-!
# op2130_flip_influence_projection

Topic: online_algorithms   Node: b154ccc51dad

Provenance: helper lemma. OP-2130, unused coin coordinates in the signal construction

If a function of a longer fair coin tape depends only on injectively selected coordinates, then the total squared influence on the longer tape is its influence on the selected coordinates multiplied by the number of assignments of the unused coordinates.
-/

private lemma op2130_flip_influence_projection_sum_range (N T : ℕ) (e : Fin N ↪ Fin T) (G : Fin T → ℕ)
    (hzero : ∀ i, i ∉ Set.range e → G i = 0) :
    (∑ i : Fin T, G i) = ∑ j : Fin N, G (e j) := by
  symm
  exact Fintype.sum_of_injective e e.injective (fun j => G (e j)) G hzero (fun j => rfl)

private lemma op2130_flip_influence_projection_update_comp (N T : ℕ) (e : Fin N ↪ Fin T)
    (r : Fin T → Bool) (j : Fin N) :
    (fun k => (Function.update r (e j) (!(r (e j)))) (e k))
      = Function.update (fun k => r (e k)) j (!(r (e j))) := by
  funext k
  rw [Function.update_apply, Function.update_apply]
  by_cases hk : k = j
  · subst hk
    simp
  · have hne : e k ≠ e j := fun h => hk (e.injective h)
    simp [hk, hne]

private lemma op2130_flip_influence_projection_sum_flip (N T : ℕ) (e : Fin N ↪ Fin T)
    (f : (Fin N → Bool) → ℤ) (r : Fin T → Bool) :
    (∑ i : Fin T, (f (fun j => r (e j)) -
       f (fun j => (Function.update r i (!(r i))) (e j))).natAbs ^ 2)
    = ∑ j : Fin N,
       (f (fun k => r (e k)) -
        f (Function.update (fun k => r (e k)) j (!((fun k => r (e k)) j)))).natAbs ^ 2 := by
  let s : Fin N → Bool := fun k => r (e k)
  let G : Fin T → ℕ := fun i =>
    (f s - f (fun j => (Function.update r i (!(r i))) (e j))).natAbs ^ 2
  have hrange : (∑ i : Fin T, G i) = ∑ j : Fin N, G (e j) := by
    apply op2130_flip_influence_projection_sum_range
    intro i hi
    have hfun : (fun j => (Function.update r i (!(r i))) (e j)) = (fun j => r (e j)) := by
      funext j
      rw [Function.update_apply]
      have hne : e j ≠ i := by
        intro h
        exact hi ⟨j, h⟩
      simp [hne]
    dsimp [G, s]
    rw [hfun]
    simp
  calc
    (∑ i : Fin T, (f (fun j => r (e j)) -
       f (fun j => (Function.update r i (!(r i))) (e j))).natAbs ^ 2)
        = ∑ i : Fin T, G i := rfl
    _ = ∑ j : Fin N, G (e j) := hrange
    _ = ∑ j : Fin N,
       (f s - f (Function.update s j (!(s j)))).natAbs ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          dsimp [G]
          rw [op2130_flip_influence_projection_update_comp]
    _ = ∑ j : Fin N,
       (f (fun k => r (e k)) -
        f (Function.update (fun k => r (e k)) j (!((fun k => r (e k)) j)))).natAbs ^ 2 := rfl

private lemma op2130_flip_influence_projection_projection (N T : ℕ) (e : Fin N ↪ Fin T)
    (g : (Fin N → Bool) → ℕ) :
    (∑ r : Fin T → Bool, g (fun j => r (e j))) =
      2 ^ (T - N) * ∑ s : Fin N → Bool, g s := by
  let S : Set (Fin T) := Set.range e
  let C := {i : Fin T // i ∉ S}
  let ee : Fin N ≃ S := Equiv.ofInjective e e.injective
  let ePre : (S → Bool) ≃ (Fin N → Bool) :=
    (Equiv.piCongrLeft (fun _ : S => Bool) ee).symm
  let Φ : (Fin T → Bool) ≃ (Fin N → Bool) × (C → Bool) :=
    (Equiv.piEquivPiSubtypeProd (fun i : Fin T => i ∈ S) (fun _ => Bool)).trans
      (Equiv.prodCongr ePre (Equiv.refl (C → Bool)))
  have hΦ : ∀ r : Fin T → Bool, Φ r = (fun j => r (e j), fun c => r c.1) := by
    intro r
    ext j
    · simp [Φ, ePre, ee, S, Equiv.piEquivPiSubtypeProd_apply]
    · change (Equiv.refl (C → Bool)) (fun x => r x.1) j = r j.1
      rw [Equiv.refl_apply]
  have hcardC : Fintype.card C = T - N := by
    dsimp [C, S]
    rw [Fintype.card_subtype_compl (p := fun i : Fin T => i ∈ Set.range e)]
    rw [Fintype.card_fin, Fintype.card_range, Fintype.card_fin]
  have hcard : Fintype.card (C → Bool) = 2 ^ (T - N) := by
    rw [Fintype.card_fun, Fintype.card_bool, hcardC]
  calc
    (∑ r : Fin T → Bool, g (fun j => r (e j)))
        = ∑ r : Fin T → Bool, g ((Φ r).1) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [hΦ r]
    _ = ∑ p : (Fin N → Bool) × (C → Bool), g p.1 := by
          apply Fintype.sum_equiv Φ (fun r => g ((Φ r).1)) (fun p => g p.1)
          intro r
          rfl
    _ = ∑ s : Fin N → Bool, ∑ t : C → Bool, g s := by
          rw [Fintype.sum_prod_type]
    _ = ∑ s : Fin N → Bool, 2 ^ (T - N) * g s := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
          simp
    _ = 2 ^ (T - N) * ∑ s : Fin N → Bool, g s := by
          rw [Finset.mul_sum]

theorem op2130_flip_influence_projection (N T : ℕ) (e : Fin N ↪ Fin T) (f : (Fin N → Bool) → ℤ) : (∑ r : Fin T → Bool, ∑ i : Fin T, (f (fun j => r (e j)) - f (fun j => (Function.update r i (!(r i))) (e j))).natAbs ^ 2) = 2 ^ (T - N) * ∑ s : Fin N → Bool, ∑ j : Fin N, (f s - f (Function.update s j (!(s j)))).natAbs ^ 2 := by
  let F : (Fin N → Bool) → Fin N → ℕ := fun s j =>
    (f s - f (Function.update s j (!(s j)))).natAbs ^ 2
  calc
    (∑ r : Fin T → Bool, ∑ i : Fin T,
        (f (fun j => r (e j)) -
         f (fun j => (Function.update r i (!(r i))) (e j))).natAbs ^ 2)
        = ∑ r : Fin T → Bool, ∑ j : Fin N, F (fun k => r (e k)) j := by
          apply Finset.sum_congr rfl
          intro r _
          exact op2130_flip_influence_projection_sum_flip N T e f r
    _ = ∑ j : Fin N, ∑ r : Fin T → Bool, F (fun k => r (e k)) j := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin N, 2 ^ (T - N) * ∑ s : Fin N → Bool, F s j := by
          apply Finset.sum_congr rfl
          intro j _
          exact op2130_flip_influence_projection_projection N T e (fun s => F s j)
    _ = 2 ^ (T - N) * ∑ j : Fin N, ∑ s : Fin N → Bool, F s j := by
          rw [Finset.mul_sum]
    _ = 2 ^ (T - N) * ∑ s : Fin N → Bool, ∑ j : Fin N, F s j := by
          rw [Finset.sum_comm]
