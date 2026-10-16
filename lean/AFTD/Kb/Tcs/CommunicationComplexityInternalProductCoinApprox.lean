import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityCoinTape
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpaceMeasureRealFinset
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpaceMeasureRealIUnionFintype
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpaceMeasureRealPreimageFinset
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpaceMeasureRealProd
import AFTD.Kb.Tcs.CommunicationComplexityInternalSingleCoinApprox
import AFTD.Kb.Tcs.CommunicationComplexityInternalWeightedSumApprox
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeMeasure
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeIsProbabilityMeasure
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityInstProd
import AFTD.Kb.Tcs.CommunicationComplexityInstPi
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpace
import AFTD.Kb.Tcs.CslibOmegaSequenceStepMk

/-!
# CommunicationComplexity.Internal.product_coin_approx

Topic: communication   Node: 59b73d0633ca

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Internal.product_coin_approx`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Product-space coin approximation. Let $\Omega_X$ and $\Omega_Y$ be finite probability spaces, and let $\delta > 0$. Give
each coin-tape space $\mathrm{CoinTape}(n)$ the uniform probability measure arising from
$n$ independent fair coin flips (mass $2^{-n}$ on each string), and give every product
space — both $\Omega_X \times \Omega_Y$ and $\mathrm{CoinTape}(n_X) \times
\mathrm{CoinTape}(n_Y)$ — the corresponding product measure. Then there exist $n_X, n_Y
\in \bbn$ and maps $\varphi_X : \mathrm{CoinTape}(n_X) \to \Omega_X$ and $\varphi_Y :
\mathrm{CoinTape}(n_Y) \to \Omega_Y$ such that, writing $\varphi_X \times \varphi_Y$ for
the map $(u,v) \mapsto (\varphi_X(u), \varphi_Y(v))$, every subset $S \subseteq \Omega_X
\times \Omega_Y$ satisfies
\[
  \Pr\!\big[(\varphi_X \times \varphi_Y)^{-1}(S)\big] \;\le\; \Pr[S] + \delta .
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ENNReal in
/-- Product version of `single_coin_approx`: for finite probability spaces `Ω_X`, `Ω_Y` and `δ > 0`, there exist coin-tape lengths `nX`, `nY` and maps `φ_X`, `φ_Y` such that for every set `S ⊆ Ω_X × Ω_Y`, the probability that `(φ_X, φ_Y)` of a pair of uniformly random tapes lies in `S` exceeds the probability of `S` by at most `δ`. **Proof sketch.** Setup: take `φ_X`, `φ_Y` from `single_coin_approx` with slack `δ/2` each. Slice `S` by its first coordinate, `S_a = {b | (a, b) ∈ S}`; the preimage of `S` is the disjoint union over `a` of the rectangles `φ_X⁻¹{a} × φ_Y⁻¹(S_a)`, so its probability is `Σ_a pX(a) · vol(φ_Y⁻¹ S_a)` with `pX(a) = vol(φ_X⁻¹{a})`, and likewise `vol S = Σ_a qX(a) · vol(S_a)` with `qX(a) = vol{a}`. Step 1: bound each slice using the `φ_Y` approximation, `vol(φ_Y⁻¹ S_a) ≤ vol(S_a) + δ/2`, and use `Σ_a pX(a) = 1` to pull the `δ/2` out. Step 2: the weights `g(a) = vol(S_a)` lie in `[0, 1]` and `pX` approximates `qX` on every finite set by the `φ_X` approximation, so `weighted_sum_approx` gives `Σ pX g ≤ Σ qX g + δ/2`. Combine the two halves. -/
theorem CommunicationComplexity.Internal.product_coin_approx
    {Ω_X Ω_Y : Type*}
    [FiniteProbabilitySpace Ω_X] [FiniteProbabilitySpace Ω_Y]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (nX nY : ℕ) (φ_X : CoinTape nX → Ω_X)
      (φ_Y : CoinTape nY → Ω_Y),
      ∀ (S : Set (Ω_X × Ω_Y)),
        volume.real (Prod.map φ_X φ_Y ⁻¹' S :
          Set (CoinTape nX × CoinTape nY)) ≤
        volume.real S + δ := by
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  obtain ⟨nX, φ_X, hX⟩ := single_coin_approx (Ω := Ω_X) (δ / 2) hδ2
  obtain ⟨nY, φ_Y, hY⟩ := single_coin_approx (Ω := Ω_Y) (δ / 2) hδ2
  refine ⟨nX, nY, φ_X, φ_Y, fun S => ?_⟩
  -- Setup: slice S_a = {b | (a,b) ∈ S}
  set S_a : Ω_X → Set Ω_Y := fun a => Prod.mk a ⁻¹' S
  -- Decompose preimage as union of rectangles
  have hunion : (Prod.map φ_X φ_Y ⁻¹' S : Set (CoinTape nX × CoinTape nY)) =
      ⋃ a : Ω_X, (φ_X ⁻¹' {a}) ×ˢ (φ_Y ⁻¹' S_a a) := by
    ext ⟨cx, cy⟩; simp [S_a, Set.mem_preimage, Set.mem_iUnion]
  have hdisj : Pairwise (fun a b : Ω_X => Disjoint
      ((φ_X ⁻¹' {a}) ×ˢ (φ_Y ⁻¹' S_a a)) ((φ_X ⁻¹' {b}) ×ˢ (φ_Y ⁻¹' S_a b))) := by
    intro a b hab; rw [Set.disjoint_left]
    rintro ⟨cx, cy⟩ h1 h2
    have hcx : φ_X cx = a := by
      simpa only [Set.mem_prod, Set.mem_preimage, Set.mem_singleton_iff] using h1.1
    have hcx' : φ_X cx = b := by
      simpa only [Set.mem_prod, Set.mem_preimage, Set.mem_singleton_iff] using h2.1
    exact hab (hcx.symm.trans hcx')
  -- LHS = ∑_a vol(φ_X⁻¹({a})) * vol(φ_Y⁻¹(S_a))
  have hLHS : volume.real (Prod.map φ_X φ_Y ⁻¹' S :
      Set (CoinTape nX × CoinTape nY)) =
      ∑ a : Ω_X, volume.real (φ_X ⁻¹' {a} : Set (CoinTape nX)) *
        volume.real (φ_Y ⁻¹' S_a a : Set (CoinTape nY)) := by
    rw [hunion]; erw [FiniteProbabilitySpace.measureReal_iUnion_fintype _ hdisj]
    refine Finset.sum_congr rfl ?_
    intro a ha
    exact FiniteProbabilitySpace.measureReal_prod
      (φ_X ⁻¹' ({a} : Set Ω_X)) (φ_Y ⁻¹' S_a a)
  -- RHS = ∑_a vol({a}) * vol(S_a)
  have hRHS : volume.real S = ∑ a : Ω_X, volume.real ({a} : Set Ω_X) *
      volume.real (S_a a) := by
    have hS : S = ⋃ a : Ω_X, ({a} : Set Ω_X) ×ˢ S_a a := by
      ext ⟨x, y⟩; simp [S_a]
    have hdisj' : Pairwise (fun a b : Ω_X => Disjoint
        (({a} : Set Ω_X) ×ˢ S_a a) (({b} : Set Ω_X) ×ˢ S_a b)) := by
      intro a b hab; rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      have hx : x = a := by
        simpa only [Set.mem_prod, Set.mem_singleton_iff] using h1.1
      have hx' : x = b := by
        simpa only [Set.mem_prod, Set.mem_singleton_iff] using h2.1
      exact hab (hx.symm.trans hx')
    rw [hS]; erw [FiniteProbabilitySpace.measureReal_iUnion_fintype _ hdisj']
    refine Finset.sum_congr rfl ?_
    intro a ha
    exact FiniteProbabilitySpace.measureReal_prod ({a} : Set Ω_X) (S_a a)
  -- Step 1: bound using hY on each slice
  set pX := fun a => volume.real (φ_X ⁻¹' {a} : Set (CoinTape nX))
  set qX := fun a => volume.real ({a} : Set Ω_X)
  rw [hLHS]
  have hstep1 : ∑ a : Ω_X, pX a * volume.real (φ_Y ⁻¹' S_a a : Set (CoinTape nY)) ≤
      ∑ a : Ω_X, pX a * (volume.real (S_a a) + δ / 2) :=
    Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hY _)
      (by simp [pX, Measure.real]))
  -- ∑ pX * (g + δ/2) = ∑ pX * g + δ/2 (since ∑ pX = 1)
  have hpX_sum : ∑ a : Ω_X, pX a = 1 := by
    calc ∑ a : Ω_X, pX a
        = volume.real (φ_X ⁻¹' (Set.univ : Set Ω_X) : Set (CoinTape nX)) := by
            have h := FiniteProbabilitySpace.measureReal_preimage_finset
                (Ξ := CoinTape nX) (Ω := Ω_X) φ_X Finset.univ
            rw [Finset.coe_univ] at h
            exact h.symm
      _ = 1 := by simp
  have hexpand : ∑ a, pX a * (volume.real (S_a a) + δ / 2) =
      (∑ a, pX a * volume.real (S_a a)) + δ / 2 := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hpX_sum, one_mul]
  -- Step 2: bound ∑ pX * g ≤ ∑ qX * g + δ/2 using weighted_sum_approx
  set gval := fun a : Ω_X => volume.real (S_a a)
  have hstep2 : ∑ a, pX a * gval a ≤ ∑ a, qX a * gval a + δ / 2 := by
    apply weighted_sum_approx pX qX gval
      (fun _ => MeasureTheory.measureReal_nonneg)
      (fun a => by
        calc gval a = volume.real (S_a a) := rfl
          _ ≤ volume.real (Set.univ : Set Ω_Y) := by
              rw [Measure.real, Measure.real]
              exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
          _ = 1 := by simp)
      (δ / 2)
      (fun T => by
        have := hX (↑T : Set Ω_X)
        simp only [pX, qX]
        -- Convert both finite-set measures into sums over singleton fibers.
        erw [FiniteProbabilitySpace.measureReal_preimage_finset
          (Ξ := CoinTape nX) (Ω := Ω_X) φ_X T] at this
        rw [FiniteProbabilitySpace.measureReal_finset (Ω := Ω_X) T] at this
        exact this)
  -- Combine the two halves
  calc ∑ a, pX a * volume.real (φ_Y ⁻¹' S_a a : Set (CoinTape nY))
      ≤ (∑ a, pX a * gval a) + δ / 2 := by linarith [hstep1, hexpand]
    _ ≤ (∑ a, qX a * gval a) + δ / 2 + δ / 2 := by linarith [hstep2]
    _ = (∑ a, qX a * gval a) + δ := by ring
    _ = volume.real S + δ := by rw [hRHS]
