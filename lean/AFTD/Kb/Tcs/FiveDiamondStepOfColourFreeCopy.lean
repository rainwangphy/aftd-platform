import AFTD.Prelude
import AFTD.Kb.Tcs.DiamondPoset
import AFTD.Kb.Tcs.InstPartialOrderDiamondPoset
import AFTD.Kb.Tcs.PosetRamseyProperty

/-!
# five_diamond_step_of_colour_free_copy

Topic: combinatorics   Node: 738e7577c376

Provenance: helper lemma. step towards five_diamond_ramsey_property_step

Assembly: if the induction hypothesis holds at (k, 4k) and every D5-free (k+1)-colouring of the subsets of Fin(4(k+1)) has an order-embedded copy of the Boolean lattice B_{4k} on which one colour is never used, then the (k+1)-colour Ramsey property holds at dimension 4(k+1).
-/

/-- Reduction of the induction step to a single combinatorial crux: a D5-free (k+1)-colouring misses a colour on some order-embedded B_{4k}. -/
theorem five_diamond_step_of_colour_free_copy (k : ℕ) (hk : 2 ≤ k)
    (ih : poset_ramsey_property (DiamondPoset 5) k (4 * k))
    (hc : ∀ (c : Finset (Fin (4 * (k + 1))) → Fin (k + 1)),
        (∀ (f : DiamondPoset 5 ↪o Finset (Fin (4 * (k + 1)))) (col : Fin (k + 1)),
          ∃ x : DiamondPoset 5, c (f x) ≠ col) →
        ∃ (e : Finset (Fin (4 * k)) ↪o Finset (Fin (4 * (k + 1)))) (a : Fin (k + 1)),
          ∀ A : Finset (Fin (4 * k)), c (e A) ≠ a) :
    poset_ramsey_property (DiamondPoset 5) (k + 1) (4 * (k + 1)) := by
  classical
  intro c
  by_cases hfree : ∃ (f : DiamondPoset 5 ↪o Finset (Fin (4 * (k + 1)))) (col : Fin (k + 1)),
      ∀ x : DiamondPoset 5, c (f x) = col
  · exact hfree
  · push Not at hfree
    obtain ⟨e, a, he⟩ := hc c hfree
    have hcard : Fintype.card {b : Fin (k + 1) // b ≠ a} = k := by
      rw [Fintype.card_subtype]
      simp only [Finset.filter_ne']
      rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
      omega
    let φ : {b : Fin (k + 1) // b ≠ a} ≃ Fin k := Fintype.equivFinOfCardEq hcard
    let c' : Finset (Fin (4 * k)) → Fin k := fun A => φ ⟨c (e A), he A⟩
    obtain ⟨g, col, hg⟩ := ih c'
    refine ⟨g.comp e, (φ.symm col).val, ?_⟩
    intro x
    have h1 : φ.symm col = ⟨c (e (g x)), he (g x)⟩ := by
      rw [← hg x]
      exact φ.symm_apply_apply _
    show c (e (g x)) = (φ.symm col).val
    rw [h1]
