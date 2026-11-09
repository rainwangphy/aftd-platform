import AFTD.Prelude

/-!
# hardCoreVarSize

Topic: statistical_mechanics   Node: eb59d404d60a

Provenance: formalization of a published result. Source: OP-1340; Scott-Sokal 2005 (arXiv:cond-mat/0309352); knowledgebase

Given a finite graph G on a type V with decidable equality and vertex fugacities lam, the variance of the independent set size hardCoreVarSize G lam is defined as the second moment minus the square of the first moment of the cardinality |I| of an independent set I chosen with probability proportional to ∏_{v ∈ I} lam v.
-/

/-- The variance of the independent set size |I| in the inhomogeneous hard-core model on G with vertex fugacities lam. -/
noncomputable def hardCoreVarSize {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam : V → ℝ) : ℝ :=
  let indep := Finset.univ.filter (fun I : Finset V => G.IsIndepSet (I : Set V))
  let Z := ∑ I ∈ indep, ∏ v ∈ I, lam v
  let E1 := (∑ I ∈ indep, (∏ v ∈ I, lam v) * (I.card : ℝ)) / Z
  let E2 := (∑ I ∈ indep, (∏ v ∈ I, lam v) * ((I.card : ℝ) ^ 2)) / Z
  E2 - E1 ^ 2
