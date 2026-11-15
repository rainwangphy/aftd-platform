import AFTD.Prelude

/-!
# op75_run

Topic: np_completeness   Node: 076209750a71

Provenance: helper lemma. OP-75, arXiv:2610.06092, one-pass subset-sum construction; a helper toward interval verification.

For a map F, a digit function E, and real weights, iteratively apply F and return the final orbit value together with the sum of the weight times the digit observed at each step.
-/

def op75_run (F E : ℝ → ℝ) : List ℝ → ℝ → ℝ × ℝ
  | [], x => (x, 0)
  | a :: as, x =>
      let r := op75_run F E as (F x)
      (r.1, a * E x + r.2)
