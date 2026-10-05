import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8GmmsCheckAll
import AFTD.Kb.GameTheoryEconomics.Poc8GmmsOk

/-!
# poc8_gmms_check

Topic: fair_division   Node: d8d134e9463a

Every bipartition (P, not P) of the eight vertices passes the bipartition check.
-/

theorem poc8_gmms_check (P : Fin 8 → Bool) : poc8_gmms_ok P = true := by
  have hP : P = ![P 0, P 1, P 2, P 3, P 4, P 5, P 6, P 7] := by
    funext x; fin_cases x <;> rfl
  rw [hP]
  exact poc8_gmms_check_all _ _ _ _ _ _ _ _
