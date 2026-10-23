import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BooleanProductBernoulli

/-!
# boolean_influence

Topic: combinatorial_games   Node: 26438d3e9a00

Provenance: formalization of a published result. Source: arXiv:2610.30730 Section 2

Given a finite type $U$ with decidable equality, a Boolean function $f : (U \to \mathrm{Bool}) \to \mathrm{Bool}$, coordinate $i \in U$, and parameter $p$ in the unit interval `unitInterval`, the $p$-influence `boolean_influence U f i p` is the integral with respect to `boolean_product_bernoulli U p` of $((\mathrm{if}\ f (\mathrm{Function.update}\ x\ i\ \mathrm{true})\ \mathrm{then}\ 1\ \mathrm{else}\ 0) - (\mathrm{if}\ f (\mathrm{Function.update}\ x\ i\ \mathrm{false})\ \mathrm{then}\ 1\ \mathrm{else}\ 0))$.
-/

/-- The p-influence of coordinate i on a Boolean function f under the product Bernoulli measure. -/
noncomputable def boolean_influence (U : Type*) [Fintype U] [DecidableEq U]
    (f : (U → Bool) → Bool) (i : U) (p : unitInterval) : ℝ := ∫ x, ((if f (Function.update x i true) then (1 : ℝ) else 0) -
        (if f (Function.update x i false) then (1 : ℝ) else 0)) ∂(boolean_product_bernoulli U p)
