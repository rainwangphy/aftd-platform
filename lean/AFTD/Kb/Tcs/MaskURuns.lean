import AFTD.Prelude
import AFTD.Kb.Tcs.MaskURunsAux

/-!
# mask_u_runs

Topic: automata   Node: 3929ca921f7b

Provenance: formalization of a published result. Source: arXiv:2610.39941, Section 3

The number of maximal nonempty U-runs in a binary mask M is defined by mask_u_runs M = mask_u_runs_aux false M, counting contiguous blocks of true starting with initial previous label false.
-/

/-- The number of maximal nonempty U-runs (contiguous blocks of true) in a binary mask. -/
def mask_u_runs (M : List Bool) : ℕ :=
  mask_u_runs_aux false M
