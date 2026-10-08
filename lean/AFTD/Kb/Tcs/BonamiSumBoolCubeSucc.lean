import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube

/-!
# Bonami.sum_boolCube_succ

Topic: combinatorics   Node: d817bb7fd95a

Provenance: helper lemma. TCSlib, `Bonami.sum_boolCube_succ`. Lean proof by Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Decomposition.lean (Apache-2.0); 1 verbatim; compiled here.

Splitting a sum over the hypercube on its last coordinate. Let $n$ be a natural number and let $\varphi \colon \{0,1\}^{n+1} \to \bbr$ be a
real-valued function on the Boolean hypercube of dimension $n+1$. Then the sum of
$\varphi$ over all points of the cube splits according to the value of the final
coordinate:
\[
\sum_{x \in \{0,1\}^{n+1}} \varphi(x) \;=\; \sum_{y \in \{0,1\}^{n}}
\varphi\bigl((y,\mathrm{false})\bigr) \;+\; \sum_{y \in \{0,1\}^{n}}
\varphi\bigl((y,\mathrm{true})\bigr),
\]
where $(y,b)$ denotes the point of $\{0,1\}^{n+1}$ obtained by appending the bit $b$ to
$y \in \{0,1\}^{n}$ as its last coordinate.
-/

open BooleanAnalysis in
/-- Splits a sum over an `(n + 1)`-dimensional Boolean cube by its final coordinate. **Source:** [OD14, Cor. 9.6 (proof)]. -/
lemma Bonami.sum_boolCube_succ {n : ℕ} (φ : BoolCube (n + 1) → ℝ) :
    ∑ x : BoolCube (n + 1), φ x =
    ∑ x : BoolCube n, φ (Fin.snoc x false) + ∑ x : BoolCube n, φ (Fin.snoc x true) := by
  have h_split :
      ∑ x : BoolCube (n + 1), φ x = ∑ x : BoolCube n × Bool, φ (Fin.snoc x.1 x.2) := by
    apply Finset.sum_bij (fun x _ => (Fin.init x, x (Fin.last n)))
    · simp +zetaDelta at *
    · simp +contextual [funext_iff]
      exact fun a₁ a₂ h₁ h₂ x => by
        cases x using Fin.lastCases <;> simp_all +decide [Fin.init]
    · intro b hb
      use Fin.snoc b.1 b.2
      aesop
    · aesop
  simp_all +decide [← Finset.sum_add_distrib]
  erw [Finset.sum_product]
  exact Finset.sum_congr rfl fun _ _ => by rw [Finset.sum_eq_add] <;> aesop
