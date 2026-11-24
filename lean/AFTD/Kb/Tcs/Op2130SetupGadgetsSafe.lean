import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130SetupFiniteGadgets
import AFTD.Kb.Tcs.Op2130IntervalMarginalRecursiveCounterexample
import AFTD.Kb.Tcs.C

/-!
# op2130_setup_gadgets_safe

Topic: online_algorithms   Node: e0fd48470984

Provenance: helper lemma. OP-2130, uniformly bounded decision-circuit preparation

In the fixed prefix, repeatable block, and final block that prepare the decision circuit, every intermediate discrepancy coordinate lies between -5 and 5.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def op2130_setup_safe (d : List ℤ) : Bool :=
  d.all fun x => decide (-5 ≤ x ∧ x ≤ 5)

def op2130_setup_scan (d : List ℤ) (es : List (ℕ × Bool)) : List (List ℤ) :=
  es.scanl (fun v (j,c) => op2130_mc_step v j c) d

theorem op2130_setup_gadgets_safe :
    (op2130_setup_scan (List.replicate 23 0) op2130_setup_pre).all op2130_setup_safe = true ∧
    (op2130_setup_scan [3,2,1,0,-1,-2,-3,-4,-1,0,0,0,0,0,0,0,0,0,0,0]
      op2130_setup_block).all op2130_setup_safe = true ∧
    (op2130_setup_scan [3,2,1,0,-1,-2,-3,-4,-1,0,0,0,0,0,0,0,0,0,0,0]
      op2130_setup_finish).all op2130_setup_safe = true := by
  decide
