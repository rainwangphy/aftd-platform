import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace

/-!
# CommunicationComplexity.FiniteProbabilitySpace.hasSum_measure_singletons

Topic: communication   Node: f16f1e4009ef

Provenance: helper lemma. TCSlib, `CommunicationComplexity.FiniteProbabilitySpace.hasSum_measure_singletons`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Singleton masses of a finite probability space sum to one. Let $\Omega$ be a finite probability space, so that $\Omega$ is finite and discrete and
its canonical volume measure $\mathbb{P}$ is a probability measure, and let $\alpha$ be
a finite type equipped with a bijection $e : \Omega \xrightarrow{\sim} \alpha$. Then the
family of singleton masses $\bigl(\mathbb{P}(\{e^{-1}(a)\})\bigr)_{a \in \alpha}$ is
summable with sum $1$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ProbabilityTheory in
/-- The singleton masses of a finite probability space sum to `1` along any finite enumeration. -/
theorem CommunicationComplexity.FiniteProbabilitySpace.hasSum_measure_singletons
    {Ω α : Type*} [FiniteProbabilitySpace Ω] [Finite α]
    (e : Ω ≃ α) :
    HasSum (fun a : α => volume ({e.symm a} : Set Ω)) 1 := by
  have huniv : (Set.univ : Set Ω) = ⋃ a : α, {e.symm a} := by
    ext x
    simp
  rw [show 1 = volume (Set.univ : Set Ω) from measure_univ.symm]
  rw [huniv]
  rw [measure_iUnion
    (fun a b hab => Set.disjoint_singleton.mpr (e.symm.injective.ne hab))
    (fun _ => MeasurableSet.of_discrete)]
  exact ENNReal.summable.hasSum
