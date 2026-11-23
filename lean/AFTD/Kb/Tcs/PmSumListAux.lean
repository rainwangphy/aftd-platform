import AFTD.Prelude
import AFTD.Kb.Tcs.MkEdge
import AFTD.Kb.Tcs.WeightsN

/-!
# pmSumListAux

Topic: quantum   Node: 2f62f0bd4f40

Provenance: formalization of a published result. Source: arXiv:2611.26300

pmSumListAux takes a semiring α, natural numbers N and D, a weight function W : WeightsN N D α, a vertex coloring ι : Fin N → Fin D, a step count n : ℕ, and a vertex list L : List (Fin N), returning an element of α defined by recursion on (n, L): 1 if n = 0; 0 if n = 1; 1 if n ≥ 2 and L = []; 0 if n ≥ 2 and L = [_]; and if n + 2 and L = v :: vs, the sum over u ∈ vs of W (mkEdge v u (ι v) (ι u)) * pmSumListAux W ι n (vs.erase u).
-/

/-- Recursive helper for computing the sum of weights over all perfect matchings. -/
def pmSumListAux {α : Type*} [Semiring α] {N D : ℕ} (W : WeightsN N D α) (ι : Fin N → Fin D) : ℕ → List (Fin N) → α
| 0, _ => 1
| 1, _ => 0
| _ + 2, [] => 1
| _ + 2, [_] => 0
| n + 2, v :: vs =>
  (vs.map (fun u =>
    W (mkEdge v u (ι v) (ι u)) * pmSumListAux W ι n (vs.erase u))).sum
