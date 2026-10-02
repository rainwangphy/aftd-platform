import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSubmodular

/-!
# submod_add_items_le

Topic: fair_division   Node: 851ed0f61acb

For a submodular set function, if every item of G lies outside A and adds at most delta >= 0 to A, then adding G to any superset W of A gains at most |G| delta.
-/

/-- If every item of `G` lies outside `A` and adds at most `δ ≥ 0` to `A`, then adding `G` to any superset `W` of `A` gains at most `|G| δ`. -/
theorem submod_add_items_le {m : ℕ} (v : Finset (Fin m) → ℝ)
    (hsub : is_submodular v) {A W : Finset (Fin m)} (hAW : A ⊆ W) {δ : ℝ} (hδ : 0 ≤ δ)
    (G : Finset (Fin m)) (hG : ∀ g ∈ G, g ∉ A ∧ v (insert g A) ≤ v A + δ) :
    v (W ∪ G) ≤ v W + G.card * δ := by
  induction G using Finset.induction_on with
  | empty => simp
  | insert a G ha ih =>
    have ih' := ih (fun g hg => hG g (Finset.mem_insert_of_mem hg))
    obtain ⟨haA, hadd⟩ := hG a (Finset.mem_insert_self a G)
    rw [Finset.union_insert, Finset.card_insert_of_notMem ha]
    push_cast
    by_cases haWG : a ∈ W ∪ G
    · rw [Finset.insert_eq_of_mem haWG]; nlinarith
    · have h := hsub A (W ∪ G) a (hAW.trans Finset.subset_union_left) haWG
      linarith
