import AFTD.Prelude

/-!
# ArrowTheorem.prod_finset_eq_prod_univ_ite

Topic: social_choice   Node: 1e529993d6c1

Provenance: helper lemma. TCSlib, `ArrowTheorem.prod_finset_eq_prod_univ_ite`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Product over a finset as an indicator product. Let $A \subseteq \mathrm{Fin}\,n$ be a finite set of indices and let $g :
\mathrm{Fin}\,n \to \bbr$. Then
\[
  \prod_{j \in A} g(j) \;=\; \prod_{j : \mathrm{Fin}\,n}
    \begin{cases} g(j) & \text{if } j \in A, \\ 1 & \text{if } j \notin A, \end{cases}
\]
so that a product taken only over the members of $A$ may equivalently be written as a
product over all of $\mathrm{Fin}\,n$ in which each factor outside $A$ is replaced by
$1$.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- Key helper: rewrite a product over a Finset as a product over Fin n with indicator. -/
lemma ArrowTheorem.prod_finset_eq_prod_univ_ite {n : ℕ} (A : Finset (Fin n)) (g : Fin n → ℝ) :
    ∏ j ∈ A, g j = ∏ j : Fin n, if j ∈ A then g j else 1 := by
  rw [← Finset.prod_filter]; congr 1; simp
