import AFTD.Prelude
import AFTD.Kb.Tcs.HigherBruhatRightCoord
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# higher_bruhat_right_coord_monotone

Topic: combinatorics   Node: d754c815d077

Provenance: formalization of a published result. Source: arXiv:2611.17465 Section 2.2

For any subset Q ⊆ {0, ..., n-1}, the right coordinate map rho_Q is monotone with respect to family inclusion under the lexicographical order on boolean lists: if X ⊆ Y, then rho_Q(X) ≤ rho_Q(Y).
-/

lemma higher_bruhat_right_coord_list_map_le_list_map {α : Type*} (l : List α) (f g : α → Bool)
    (h : ∀ x ∈ l, f x ≤ g x) :
    l.map f ≤ l.map g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    have hx : f x ≤ g x := h x (List.Mem.head xs)
    have hxs : ∀ y ∈ xs, f y ≤ g y := fun y hy => h y (List.Mem.tail x hy)
    have ih' := ih hxs
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact le_of_lt (List.Lex.rel hlt)
    · rw [heq]
      exact List.cons_le_cons (g x) ih'

/-- Each right coordinate rho_Q is order-preserving under inclusion. -/
theorem higher_bruhat_right_coord_monotone (n : ℕ) (Q : Finset (Fin n))
    {X Y : Finset (Finset (Fin n))} (h : X ⊆ Y) :
    higher_bruhat_right_coord n Q X ≤ higher_bruhat_right_coord n Q Y := by
  dsimp [higher_bruhat_right_coord]
  split_ifs with hQ
  · apply higher_bruhat_right_coord_list_map_le_list_map
    intro x _hx
    rw [Bool.le_iff_imp, decide_eq_true_iff, decide_eq_true_iff]
    intro hx_mem
    exact h hx_mem
  · rfl
