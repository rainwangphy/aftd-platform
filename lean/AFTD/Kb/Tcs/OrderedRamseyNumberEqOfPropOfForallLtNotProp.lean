import AFTD.Prelude
import AFTD.Kb.Tcs.OrderedRamseyNumber
import AFTD.Kb.Tcs.OrderedRamseyProp

/-!
# ordered_ramsey_number_eq_of_prop_of_forall_lt_not_prop

Topic: graphs   Node: 580a09bf40c5

Provenance: helper lemma. step towards ordered_ramsey_monotone_cycle_alternating_path

An ordered Ramsey number R_ord(H, H') is equal to N if the ordered Ramsey property holds at N and fails for all M < N.
-/

/-- An ordered Ramsey number is equal to N if the ordered Ramsey property holds at N and fails for all M < N. -/
theorem ordered_ramsey_number_eq_of_prop_of_forall_lt_not_prop
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (H : SimpleGraph α) (H' : SimpleGraph β) (N : ℕ)
    (hprop : ordered_ramsey_prop H H' N)
    (hmin : ∀ M < N, ¬ ordered_ramsey_prop H H' M) :
    ordered_ramsey_number H H' = N := by
  unfold ordered_ramsey_number
  apply le_antisymm
  · apply csInf_le (OrderBot.bddBelow _)
    exact hprop
  · apply le_csInf ⟨N, hprop⟩
    intro M hM
    by_contra! hlt
    exact hmin M hlt hM
