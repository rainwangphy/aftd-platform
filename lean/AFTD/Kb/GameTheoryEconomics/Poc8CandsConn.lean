import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8Cands
import AFTD.Kb.GameTheoryEconomics.Poc8Connb

/-!
# poc8_cands_conn

Topic: fair_division   Node: 5154a9a1958c

Each of the 47 stored masks and its complement pass the Boolean connectivity test (kernel computation).
-/

theorem poc8_cands_conn : ∀ m ∈ poc8_cands,
    poc8_connb (fun v => m.testBit v) = true ∧ poc8_connb (fun v => !m.testBit v) = true := by
  decide +kernel
