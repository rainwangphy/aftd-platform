import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LxvEf1
import AFTD.Kb.GameTheoryEconomics.LxvProfile
import AFTD.Kb.GameTheoryEconomics.LxvOpt

/-!
# lxv_check

Topic: fair_division   Node: 6aedca5edd0c

The finite check over all 4^6 allocations: lxv_opt is EF1, no EF1 allocation has a strictly better leximin profile, and any EF1 allocation not strictly leximin-worse equals lxv_opt.
-/

/-- The finite check run by the kernel, over all `4^6` allocations. -/
def lxv_check : Bool :=
  lxv_ef1 lxv_opt &&
  (List.finRange 4).all fun a0 => (List.finRange 4).all fun a1 => (List.finRange 4).all fun a2 =>
  (List.finRange 4).all fun a3 => (List.finRange 4).all fun a4 => (List.finRange 4).all fun a5 =>
    let τ : Fin 6 → Fin 4 := ![a0, a1, a2, a3, a4, a5]
    !lxv_ef1 τ || (!decide (List.Lex (· < ·) (lxv_profile lxv_opt) (lxv_profile τ)) &&
      (decide (List.Lex (· < ·) (lxv_profile τ) (lxv_profile lxv_opt)) ||
        (List.finRange 6).all fun g => decide (τ g = lxv_opt g)))
