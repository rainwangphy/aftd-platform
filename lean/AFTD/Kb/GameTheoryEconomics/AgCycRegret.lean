import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AgCnt
import AFTD.Kb.GameTheoryEconomics.AgCyc
import AFTD.Kb.GameTheoryEconomics.AgCycV
import AFTD.Kb.GameTheoryEconomics.AgCycUEq
import AFTD.Kb.GameTheoryEconomics.AgTot
import AFTD.Kb.GameTheoryEconomics.AgCntEq
import AFTD.Kb.GameTheoryEconomics.AgSub

/-!
# agCyc_regret

Topic: equilibria   Node: 2bfe21af2586

From a regret-2 certificate on the totals to a player with regret 1/2.
-/

open Finset in
/-- From a regret-2 certificate on the totals to a player with regret `1/2`. -/
theorem agCyc_regret {s : ℕ} [NeZero s] (σ : Fin 5 → Fin s) (i j : Fin s)
    (hpos : 0 < agTot σ i)
    (hreg : agCycV i (agSub (agTot σ) i) + 2 ≤ agCycV j (agSub (agTot σ) i)) :
    ∃ p : Fin 5, (agCyc 5 s).u p (σ p) (agCnt σ p) + 1 / 2 ≤ (agCyc 5 s).u p j (agCnt σ p) := by
  obtain ⟨p, hp⟩ := Finset.card_pos.1 hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  refine ⟨p, ?_⟩
  have hc : agCnt σ p = agSub (agTot σ) i := by
    funext k
    rw [agCnt_eq, hp]
    unfold agSub
    by_cases h : i = k
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  rw [hc, hp, agCyc_u_eq, agCyc_u_eq]
  have : ((agCycV i (agSub (agTot σ) i) + 2 : ℕ) : ℚ) ≤ (agCycV j (agSub (agTot σ) i) : ℚ) := by
    exact_mod_cast hreg
  push_cast at this
  linarith
