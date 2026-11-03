import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.Order
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# exists_strictly_ordered_intervals

Topic: social_choice   Node: 42d9675e13ac

Provenance: helper lemma. step towards countable_lex_stream_order_embedding_exists

For every countable linearly ordered type A, there exists a family of strictly separated intervals [l(a), r(a)] in (0, 1/2] such that a < b implies r(a) < l(b).
-/

/-- Every countable linearly ordered type embeds into strictly separated intervals in (0, 1/2]. -/
theorem exists_strictly_ordered_intervals (A : Type) [LinearOrder A] [Countable A] :
    ∃ (l r : A → ℝ), (∀ a, 0 < l a ∧ l a < r a ∧ r a ≤ (1 / 2 : ℝ)) ∧
      (∀ a b, a < b → r a < l b) := by
  have instCountable : Countable (Lex (A × Bool)) := Countable.of_equiv (A × Bool) toLex.symm
  have instNontrivial : Nontrivial (Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) := by
    have h1 : (0 : ℝ) < 1 / 4 := by norm_num
    have h2 : (1 / 4 : ℝ) < 1 / 2 := by norm_num
    have h3 : (0 : ℝ) < 3 / 8 := by norm_num
    have h4 : (3 / 8 : ℝ) < 1 / 2 := by norm_num
    have hne : (1 / 4 : ℝ) ≠ 3 / 8 := by norm_num
    exact ⟨⟨⟨1 / 4, h1, h2⟩, ⟨3 / 8, h3, h4⟩, fun h ↦ hne (Subtype.ext_iff.mp h)⟩⟩
  obtain ⟨e⟩ := Order.embedding_from_countable_to_dense (Lex (A × Bool)) (Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
  let l : A → ℝ := fun a ↦ (e (toLex (a, false))).val
  let r : A → ℝ := fun a ↦ (e (toLex (a, true))).val
  refine ⟨l, r, ?_, ?_⟩
  · intro a
    have hmem_l := (e (toLex (a, false))).prop
    have hmem_r := (e (toLex (a, true))).prop
    have hlt : toLex (a, false) < toLex (a, true) := by
      change Prod.Lex (· < ·) (· < ·) (a, false) (a, true)
      exact Prod.Lex.right a (by decide)
    have he_lt : (e (toLex (a, false))).val < (e (toLex (a, true))).val := e.lt_iff_lt.mpr hlt
    exact ⟨hmem_l.1, he_lt, le_of_lt hmem_r.2⟩
  · intro a b hab
    have hlt : toLex (a, true) < toLex (b, false) := by
      change Prod.Lex (· < ·) (· < ·) (a, true) (b, false)
      exact Prod.Lex.left true false hab
    exact e.lt_iff_lt.mpr hlt
