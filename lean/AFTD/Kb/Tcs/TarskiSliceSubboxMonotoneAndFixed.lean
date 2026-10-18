import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiSliceLowerBound
import AFTD.Kb.Tcs.TarskiSliceUpperBound
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# tarski_slice_subbox_monotone_and_fixed

Topic: algorithms   Node: a715cd158ad1

Provenance: helper lemma. step towards tarski_box_query_le_succ_halving

For any monotone map f on [a, b] in dimension k+1 and any coordinate cut c with a_i <= c <= b_i, the sliced map g y j = f (insertNth i c y) (i.succAbove j) is monotone on [a', b'] (where a' = a ∘ i.succAbove, b' = b ∘ i.succAbove) and satisfies the sub-box invariants a' <= g a' and g b' <= b'. Moreover, any fixed point y of g lifts to an ambient point x = insertNth i c y in [a, b] that agrees with f(x) on all coordinates j != i.
-/

/-- Monotonicity and sub-box bounds for the coordinate slice map, and lifting of a slice fixed point to an ambient point fixed off coordinate i. -/
theorem tarski_slice_subbox_monotone_and_fixed (n k : ℕ) [NeZero n]
    (f : (Fin (k+1) → Fin n) → (Fin (k+1) → Fin n)) (hf : Monotone f)
    (a b : Fin (k+1) → Fin n) (ha : a ≤ f a) (hb : f b ≤ b)
    (i : Fin (k+1)) (c : Fin n) (hac : a i ≤ c) (hcb : c ≤ b i) :
    let g : (Fin k → Fin n) → (Fin k → Fin n) := fun y j => f (Fin.insertNth i c y) (i.succAbove j)
    let a' : Fin k → Fin n := a ∘ i.succAbove
    let b' : Fin k → Fin n := b ∘ i.succAbove
    Monotone g ∧ a' ≤ g a' ∧ g b' ≤ b' ∧
    ∀ y : Fin k → Fin n, a' ≤ y → y ≤ b' → g y = y →
      let x := Fin.insertNth i c y
      a ≤ x ∧ x ≤ b ∧ (∀ j : Fin (k+1), j ≠ i → f x j = x j) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y y' hyy'
    intro j
    refine hf (Fin.insertNth_le_iff.mpr ⟨?_, ?_⟩) (i.succAbove j)
    · rw [Fin.insertNth_apply_same]
    · intro l
      simp only [Fin.insertNth_apply_succAbove]
      exact hyy' l
  · intro j
    apply le_trans (ha (i.succAbove j))
    exact hf (Fin.le_insertNth_iff.mpr ⟨hac, le_refl _⟩) (i.succAbove j)
  · intro j
    apply le_trans (hf (Fin.insertNth_le_iff.mpr ⟨hcb, le_refl _⟩) (i.succAbove j))
    exact hb (i.succAbove j)
  · intro y hay hyb hgy
    refine ⟨?_, ?_, ?_⟩
    · exact Fin.le_insertNth_iff.mpr ⟨hac, hay⟩
    · exact Fin.insertNth_le_iff.mpr ⟨hcb, hyb⟩
    · intro j hj
      obtain ⟨m, hm⟩ := Fin.exists_succAbove_eq hj
      subst hm
      simp only [Fin.insertNth_apply_succAbove]
      exact congr_fun hgy m
