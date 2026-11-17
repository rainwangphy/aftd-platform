import AFTD.Prelude

/-!
# op869_orient_three_color_blocks

Topic: online_algorithms   Node: 332d8634b564

Provenance: helper lemma. arXiv:2610.41516, Lemma 2.5: reserve disjoint bipartite copies and orient them for an offline three-coloring.

For each bipartite block with a three-colored owner and at most one three-colored target of a different color, its two sides can be assigned the two colors different from the owner so that the designated side has the target color when a target exists.
-/

lemma op869_third_color_tmp (a b : Fin 3) (h : b ≠ a) :
    ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by
  fin_cases a <;> fin_cases b <;> norm_num at * <;> decide

theorem op869_orient_three_color_blocks {V B : Type} (φ : V → Fin 3) (owner : B → V)
    (target : B → Option V) (selected : B → Bool) :
    (∀ b v, target b = some v → φ v ≠ φ (owner b)) →
    ∃ left right : B → Fin 3, ∀ b,
      left b ≠ φ (owner b) ∧ right b ≠ φ (owner b) ∧ left b ≠ right b ∧
      ∀ v, target b = some v → (if selected b then left b else right b) = φ v := by
  classical
  intro h
  have local_choice : ∀ b : B, ∃ l r : Fin 3,
      l ≠ φ (owner b) ∧ r ≠ φ (owner b) ∧ l ≠ r ∧
      ∀ v, target b = some v → (if selected b then l else r) = φ v := by
    intro b
    cases ht : target b with
    | none =>
      have hn : ∃ l r : Fin 3, l ≠ φ (owner b) ∧ r ≠ φ (owner b) ∧ l ≠ r := by
        generalize hcol : φ (owner b) = col
        fin_cases col <;> simp_all <;> decide
      obtain ⟨l, r, hl, hr, hlr⟩ := hn
      exact ⟨l, r, hl, hr, hlr, by simp [ht]⟩
    | some v =>
      have hv : φ v ≠ φ (owner b) := h b v ht
      obtain ⟨c, hco, hcv⟩ := op869_third_color_tmp (φ (owner b)) (φ v) hv
      cases hs : selected b with
      | false =>
        refine ⟨c, φ v, hco, hv, hcv, ?_⟩
        intro w hw
        have : w = v := (Option.some.inj hw).symm
        subst w
        simp [hs]
      | true =>
        refine ⟨φ v, c, hv, hco, Ne.symm hcv, ?_⟩
        intro w hw
        have : w = v := (Option.some.inj hw).symm
        subst w
        simp [hs]
  choose left right hleft using local_choice
  exact ⟨left, right, hleft⟩
