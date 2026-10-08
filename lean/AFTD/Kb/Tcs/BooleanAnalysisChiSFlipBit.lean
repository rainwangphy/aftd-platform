import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisFlipBit

/-!
# BooleanAnalysis.chiS_flipBit

Topic: combinatorics   Node: 1d91ac277d76

Provenance: helper lemma. TCSlib, `BooleanAnalysis.chiS_flipBit`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Walsh character under a single bit flip. Fix a subset $S\subseteq[n]$ of coordinates. For every point $x$ of the Boolean
hypercube $\{0,1\}^n$ and every coordinate $i\in[n]$, the value of the Walsh--Fourier
character $\chi_S$ at the point $x^i$ obtained by flipping the $i$-th coordinate of $x$
is
\[
  \chi_S(x^i) \;=\;
  \begin{cases} -\chi_S(x) & i\in S,\\[2pt] \chi_S(x) & i\notin S. \end{cases}
\]
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- Flipping bit `i` negates `χ_S` when `i ∈ S`, and leaves it unchanged when `i ∉ S`. -/
lemma BooleanAnalysis.chiS_flipBit (S : Finset (Fin n)) (x : BoolCube n) (i : Fin n) :
    chiS S (flipBit x i) = if i ∈ S then -chiS S x else chiS S x := by
  simp only [chiS, flipBit]
  by_cases hiS : i ∈ S
  · simp only [hiS, ↓reduceIte]
    -- Rewrite ∏_{j∈S} boolToSign(update x i (!xi) j) using prod_update_of_mem
    have flipped_prod : ∏ j ∈ S, boolToSign (Function.update x i (!x i) j) =
        boolToSign (!x i) * ∏ j ∈ S \ {i}, boolToSign (x j) := by
      have : ∏ j ∈ S, boolToSign (Function.update x i (!x i) j) =
          ∏ j ∈ S, Function.update (fun j => boolToSign (x j)) i (boolToSign (!x i)) j := by
        apply Finset.prod_congr rfl; intro j _
        simp only [Function.update_apply]
        split_ifs with h
        · subst h; rfl
        · rfl
      rw [this]
      exact Finset.prod_update_of_mem hiS _ _
    have orig_prod : ∏ j ∈ S, boolToSign (x j) =
        boolToSign (x i) * ∏ j ∈ S \ {i}, boolToSign (x j) := by
      rw [← Finset.mul_prod_erase _ _ hiS]
      simp [Finset.erase_eq]
    have hneg : boolToSign (!x i) = -boolToSign (x i) := by cases x i <;> simp [boolToSign]
    rw [flipped_prod, orig_prod, hneg]; ring
  · simp only [hiS, ↓reduceIte]
    apply Finset.prod_congr rfl; intro j hj
    have hji : j ≠ i := fun h => hiS (h ▸ hj)
    simp [Function.update_of_ne hji]
