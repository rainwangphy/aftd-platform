import AFTD.Prelude
import AFTD.Kb.Tcs.NfaRunCountList

/-!
# nfa_run_count_fiberwise_sum

Topic: automata   Node: 5e6e901aea6e

Provenance: helper lemma. step towards nfa_run_count_list_concat

The number of runs of w ++ [a] from p to q is the sum over all states s of the number of runs whose penultimate state is s.
-/

open Classical in
/-- The total number of runs of w ++ [a] from p to q is the sum over all states s of the number of runs whose penultimate state is s. -/
theorem nfa_run_count_fiberwise_sum {α σ : Type*} [Fintype σ] (M : NFA α σ) (w : List α) (a : α)
    (p q : σ) :
    nfa_run_count_list M (w ++ [a]) p q =
      ∑ s : σ, {r : Fin ((w ++ [a]).length + 1) → σ |
        r 0 = p ∧ r (Fin.last (w ++ [a]).length) = q ∧
        (∀ i : Fin (w ++ [a]).length, r i.succ ∈ M.step (r i.castSucc) ((w ++ [a]).get i)) ∧
        r ⟨w.length, by simp⟩ = s}.ncard := by
  let S : Set (Fin ((w ++ [a]).length + 1) → σ) :=
    {r | r 0 = p ∧ r (Fin.last (w ++ [a]).length) = q ∧
      ∀ i : Fin (w ++ [a]).length, r i.succ ∈ M.step (r i.castSucc) ((w ++ [a]).get i)}
  let f : (Fin ((w ++ [a]).length + 1) → σ) → σ := fun r => r ⟨w.length, by simp⟩
  change S.ncard = ∑ s : σ, {r : Fin ((w ++ [a]).length + 1) → σ |
        r 0 = p ∧ r (Fin.last (w ++ [a]).length) = q ∧
        (∀ i : Fin (w ++ [a]).length, r i.succ ∈ M.step (r i.castSucc) ((w ++ [a]).get i)) ∧
        r ⟨w.length, by simp⟩ = s}.ncard
  rw [Set.ncard_eq_toFinset_card']
  rw [Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (f := f) (s := S.toFinset) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro s _
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext r
  simp only [Finset.mem_filter, Set.mem_toFinset]
  dsimp [S, f]
  tauto
