import AFTD.Prelude
import AFTD.Kb.Tcs.DedekindNumber
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.InstFintypeOrderHom

/-!
# dedekind_number_zero

Topic: combinatorics   Node: ba8b3dc687a9

Provenance: formalization of a published result. Source: arXiv:2611.13887 Section 2

The 0-th Dedekind number is 2.
-/

def dedekind_number_zero_orderHom_equiv (α β : Type*) [Unique α] [Preorder α] [Preorder β] :
    (α →o β) ≃ β where
  toFun f := f default
  invFun b := ⟨fun _ => b, fun _ _ _ => le_rfl⟩
  left_inv f := by
    ext x
    have : x = default := Subsingleton.elim x default
    subst this
    rfl
  right_inv b := rfl

/-- The 0-th Dedekind number is 2. -/
lemma dedekind_number_zero : dedekind_number 0 = 2 := by
  change Fintype.card ((Fin 0 → Bool) →o Bool) = 2
  rw [Fintype.card_congr (dedekind_number_zero_orderHom_equiv (Fin 0 → Bool) Bool)]
  exact Fintype.card_bool
