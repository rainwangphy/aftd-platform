import AFTD.Prelude

/-!
# greedy_indep_var

Topic: graphs   Node: e4ee52bfbd81

Provenance: formalization of a published result. Source: arXiv:2609.14826: Section 2

The variance of the cardinality of the random greedy maximal independent set of a finite simple graph on vertex set Fin n under the uniform distribution over vertex inspection orderings.
-/

open Classical in
/-- Variance of the random greedy independent set size on a graph on Fin n. -/
noncomputable def greedy_indep_var {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  let greedy_indep : Equiv.Perm (Fin n) → Finset (Fin n) := fun σ =>
    (List.ofFn σ).foldl (fun I v => if ∀ u ∈ I, ¬G.Adj u v then insert v I else I) ∅
  let N : ℝ := (Nat.factorial n : ℝ)
  let X : Equiv.Perm (Fin n) → ℝ := fun σ => ((greedy_indep σ).card : ℝ)
  let E1 : ℝ := (∑ σ, X σ) / N
  let E2 : ℝ := (∑ σ, (X σ) ^ 2) / N
  E2 - E1 ^ 2
