import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented

/-!
# op1370_coordinate_patterns_bound

Topic: combinatorics   Node: 2b7d6b366c8c

Provenance: helper lemma. Coordinate-pattern counting lemma for OP-1370.

If an uncomplemented family has the opposite membership of x at every coordinate in Y, where x is outside Y, then its size is at most 2^(n-(|Y|+1)).
-/

lemma op1370_coordinate_patterns_bound (n : ℕ) (F : Finset (Finset (Fin n)))
    (hu : is_uncomplemented F) (x : Fin n) (Y : Finset (Fin n)) (hxY : x ∉ Y)
    (hpattern : ∀ S ∈ F, ∀ y ∈ Y, (x ∈ S ↔ y ∉ S)) :
    F.card ≤ 2 ^ (n - (Y.card + 1)) := by
  open Finset in
  classical
  let V : Finset (Fin n) := univ \ insert x Y
  let f : Finset (Fin n) → Finset (Fin n) := fun S => (if x ∈ S then S else Sᶜ).erase x
  have hmap : Set.MapsTo f F V.powerset := by
    intro S hS
    apply mem_powerset.mpr
    intro a ha
    by_cases hxS : x ∈ S
    · simp only [f, hxS, ↓reduceIte, mem_erase] at ha
      simp only [V, mem_sdiff, mem_univ, mem_insert, true_and, not_or]
      refine ⟨ha.1, ?_⟩
      intro haY
      exact (hpattern S hS a haY).mp hxS ha.2
    · simp only [f, hxS, ↓reduceIte, mem_erase, mem_compl] at ha
      simp only [V, mem_sdiff, mem_univ, mem_insert, true_and, not_or]
      refine ⟨ha.1, ?_⟩
      intro haY
      have haS : a ∈ S := by
        by_contra haS
        exact hxS ((hpattern S hS a haY).mpr haS)
      exact ha.2 haS
  have hinj : (F : Set (Finset (Fin n))).InjOn f := by
    intro S hS T hT hST
    by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T
    · have he : S.erase x = T.erase x := by simpa [f, hxS, hxT] using hST
      calc S = insert x (S.erase x) := (insert_erase hxS).symm
           _ = insert x (T.erase x) := by rw [he]
           _ = T := insert_erase hxT
    · have he : S.erase x = Tᶜ.erase x := by simpa [f, hxS, hxT] using hST
      have hxTc : x ∈ Tᶜ := mem_compl.mpr hxT
      have hEq : S = Tᶜ := by
        calc S = insert x (S.erase x) := (insert_erase hxS).symm
             _ = insert x (Tᶜ.erase x) := by rw [he]
             _ = Tᶜ := insert_erase hxTc
      exact False.elim ((hu T hT) (hEq ▸ hS))
    · have he : Sᶜ.erase x = T.erase x := by simpa [f, hxS, hxT] using hST
      have hxSc : x ∈ Sᶜ := mem_compl.mpr hxS
      have hEq : Sᶜ = T := by
        calc Sᶜ = insert x (Sᶜ.erase x) := (insert_erase hxSc).symm
             _ = insert x (T.erase x) := by rw [he]
             _ = T := insert_erase hxT
      exact False.elim ((hu S hS) (hEq.symm ▸ hT))
    · have he : Sᶜ.erase x = Tᶜ.erase x := by simpa [f, hxS, hxT] using hST
      have hxSc : x ∈ Sᶜ := mem_compl.mpr hxS
      have hxTc : x ∈ Tᶜ := mem_compl.mpr hxT
      have hc : Sᶜ = Tᶜ := by
        calc Sᶜ = insert x (Sᶜ.erase x) := (insert_erase hxSc).symm
             _ = insert x (Tᶜ.erase x) := by rw [he]
             _ = Tᶜ := insert_erase hxTc
      simpa using congrArg (fun a : Finset (Fin n) => aᶜ) hc
  have hVcard : V.card = n - (Y.card + 1) := by
    dsimp [V]
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
      card_insert_of_notMem hxY]
  have hc := card_le_card_of_injOn f hmap hinj
  simpa [card_powerset, hVcard] using hc
