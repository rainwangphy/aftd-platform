import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130IntervalMarginalRecursiveCounterexample
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.C

/-!
# op2130_setup_finite_gadgets

Topic: online_algorithms   Node: 4a896f9ab1f0

Provenance: helper lemma. OP-2130, repeatable preparation of decision-list height profiles

A 96-request prefix, a repeatable 185-request block, and a 41-request ending perform the exact finite greedy discrepancy transformations displayed in the Lean statement.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def op2130_setup_pre : List (ℕ × Bool) := [(0, false), (1, false), (2, false), (1, false), (0, false), (2, false), (1, false), (3, false), (2, false), (3, false), (4, false), (3, false), (2, false), (1, false), (0, false), (1, true), (2, true), (1, true), (2, true), (3, true), (2, true), (1, true), (3, true), (2, true), (3, true), (4, true), (3, true), (2, true), (1, true), (4, true), (3, true), (2, true), (4, true), (3, true), (5, true), (4, true), (5, true), (6, true), (5, true), (4, true), (3, true), (2, true), (6, true), (5, true), (4, true), (3, true), (6, true), (5, true), (4, true), (7, true), (6, true), (5, true), (7, true), (6, true), (7, true), (8, true), (7, true), (6, true), (5, true), (4, true), (3, true), (2, true), (8, true), (7, true), (6, true), (5, true), (4, true), (3, true), (8, true), (7, true), (6, true), (5, true), (4, true), (8, true), (7, true), (6, true), (5, true), (9, true), (8, true), (7, true), (6, true), (9, true), (8, true), (7, true), (9, true), (8, true), (9, true), (10, true), (9, true), (8, true), (7, true), (6, true), (5, true), (4, true), (3, true), (2, true)]
def op2130_setup_block : List (ℕ × Bool) := [(0, false), (1, false), (0, false), (1, false), (2, false), (1, false), (0, false), (2, false), (1, false), (2, false), (3, false), (2, false), (1, false), (0, false), (3, false), (2, false), (1, false), (3, false), (2, false), (3, false), (4, false), (3, false), (2, false), (1, false), (0, false), (4, false), (3, false), (2, false), (1, false), (4, false), (3, false), (2, false), (4, false), (3, false), (4, false), (5, false), (4, false), (3, false), (2, false), (1, false), (0, false), (5, false), (4, false), (3, false), (2, false), (1, false), (5, false), (4, false), (3, false), (2, false), (5, false), (4, false), (3, false), (5, false), (4, false), (5, false), (6, false), (5, false), (4, false), (3, false), (2, false), (1, false), (0, false), (6, false), (5, false), (4, false), (3, false), (2, false), (1, false), (6, false), (5, false), (4, false), (3, false), (2, false), (6, false), (5, false), (4, false), (3, false), (6, false), (5, false), (4, false), (6, false), (5, false), (6, false), (7, false), (6, false), (5, false), (4, false), (3, false), (2, false), (1, false), (2, true), (3, true), (2, true), (3, true), (4, true), (3, true), (2, true), (4, true), (3, true), (4, true), (5, true), (4, true), (3, true), (2, true), (5, true), (4, true), (3, true), (5, true), (4, true), (5, true), (6, true), (5, true), (4, true), (3, true), (2, true), (6, true), (5, true), (4, true), (3, true), (6, true), (5, true), (4, true), (6, true), (5, true), (6, true), (7, true), (6, true), (5, true), (4, true), (3, true), (7, true), (6, true), (5, true), (4, true), (7, true), (6, true), (5, true), (8, true), (7, true), (6, true), (8, true), (7, true), (8, true), (9, true), (8, true), (7, true), (6, true), (5, true), (4, true), (3, true), (9, true), (8, true), (7, true), (6, true), (5, true), (4, true), (9, true), (8, true), (7, true), (6, true), (5, true), (9, true), (8, true), (7, true), (6, true), (10, true), (9, true), (8, true), (7, true), (10, true), (9, true), (8, true), (10, true), (9, true), (10, true), (11, true), (10, true), (9, true), (8, true), (7, true), (6, true), (5, true), (4, true), (3, true)]
def op2130_setup_finish : List (ℕ × Bool) := [(0, false), (1, false), (0, false), (1, false), (2, false), (1, false), (0, false), (2, false), (1, false), (2, false), (3, false), (2, false), (1, false), (0, false), (3, false), (2, false), (1, false), (3, false), (2, false), (3, false), (4, false), (3, false), (2, false), (1, false), (0, false), (4, false), (3, false), (2, false), (1, false), (4, false), (3, false), (2, false), (4, false), (3, false), (4, false), (5, false), (4, false), (3, false), (2, false), (1, false), (0, false)]
def op2130_setup_replay (d : List ℤ) (es : List (ℕ × Bool)) : List ℤ :=
  es.foldl (fun v (j,c) => op2130_mc_step v j c) d



theorem op2130_suffix_energy_left (a b j : ℤ) (hab : a ≤ b) :
    (a+1+j)^2 + (b-1+(j+1))^2 ≤ (a+j)^2 + (b+(j+1))^2 := by
  nlinarith

theorem op2130_suffix_energy_right (a b j : ℤ) (hab : b ≤ a) :
    (a-1-j)^2 + (b+1-(j+1))^2 ≤ (a-j)^2 + (b-(j+1))^2 := by
  nlinarith

theorem op2130_setup_finite_gadgets :
  op2130_setup_replay (List.replicate 23 0) op2130_setup_pre = [-3, 3, 5, 3, 2, 1, 0, -1, -2, -3, -4, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ∧
  op2130_setup_replay [3, 2, 1, 0, -1, -2, -3, -4, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] op2130_setup_block = [-4, -4, 3, 5, 3, 2, 1, 0, -1, -2, -3, -4, -1, 0, 0, 0, 0, 0, 0, 0] ∧
  op2130_setup_replay [3, 2, 1, 0, -1, -2, -3, -4, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] op2130_setup_finish = [-3, -1, 0, 1, 2, 3, -2, -4, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide
