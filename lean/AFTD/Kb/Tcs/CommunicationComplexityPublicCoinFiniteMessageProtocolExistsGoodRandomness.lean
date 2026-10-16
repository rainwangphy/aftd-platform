import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolDerandomizationSamples
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolProbManyEventsLe
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpaceIntegralCompEval
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpaceMeasureRealEqIntegralIndicatorOne
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolApproxComputes
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapSwap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityInstProd
import AFTD.Kb.Tcs.CommunicationComplexityInstPi
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpace
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceFintype
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolApproxComputes
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolApproxComputes
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolApproxComputes
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocolRun

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.exists_good_randomness

Topic: communication   Node: 3275890a18f3

Provenance: helper lemma. TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.exists_good_randomness`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Derandomization.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Existence of good randomness for derandomization. Let $\Omega$ be a finite probability space and let $X$ and $Y$ be finite input sets. Let
$p$ be a public-coin finite-message protocol over shared randomness $\Omega$ with
private inputs in $X$ and $Y$ and output type $\alpha$, let $f : X \to Y \to \alpha$,
and let $\varepsilon, c \in \bbr$ with $c > 1$. Suppose $p$ $\varepsilon$-computes $f$,
so that for every input pair $(x,y)$ the probability over $\omega$ that the randomized
execution $\mathrm{rrun}(p,x,y,\omega)$ differs from $f(x,y)$ is at most $\varepsilon$.
Then, writing $t = t(X,Y,\varepsilon,c)$ for the derandomization sample count, there
exists a family $\omega_0, \dots, \omega_{t-1} \in \Omega$ of shared-randomness values
such that for every $(x,y)$,
\[
\frac{\#\{\, i \mid \mathrm{rrun}(p,x,y,\omega_i) \ne f(x,y) \,\}}{t} \;\le\;
c\,\varepsilon.
\]
-/

open CommunicationComplexity CommunicationComplexity.PublicCoin CommunicationComplexity.PublicCoin.FiniteMessage CommunicationComplexity.PublicCoin.FiniteMessage.Protocol in
set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
variable {Ω X Y α : Type*}
  [Fintype X] [Fintype Y] in
open Classical in
/-- Existence of a small table of good seeds (the derandomization step of Newman's theorem): if a public-coin finite-message protocol `p` ε-computes `f` and `c > 1`, then there is a table `ωs` of `t = derandomizationSamples X Y ε c` seeds such that for every input `(x, y)`, at most a `c · ε` fraction of the seeds `ωs i` make `p` output a value different from `f x y`. [RY20, Thm 3.5 proof] (Chernoff + union bound over inputs) / [Rou16, Thm 4.9 proof]; historically [New91]. **Proof sketch.** Step 1: dispose of the degenerate cases. If `X` or `Y` is empty the claim is vacuous; if `ε ≥ 1` any table works because the bad fraction is at most `1 < c · ε`; if `ε < 0` the hypothesis contradicts the nonnegativity of probabilities; if `ε = 0` every bad set has measure zero, so by a countable union bound some single seed is correct on all inputs and the constant table works. Step 2: in the main case `0 < ε`, the choice of `t` gives the key numeric bound `exp(−2 (c−1)² ε² t) · |X| · |Y| < 1`, since `log(|X||Y|) / (2 (c−1)² ε²) < t`. Step 3: sample the `t` seeds independently, i.e. work on the product space `Fin t → Ω`. For a fixed input `(x, y)`, the indicators `Yᵢ = 1[p errs on seed ωs i]` are independent (they are functions of distinct coordinates), `[0,1]`-valued, and have mean equal to the failure probability of `p` on `(x, y)`, which is at most `ε`; the Hoeffding bound `prob_many_events_le` shows that the bad event "at least `c ε t` of the seeds err on `(x, y)`" has probability at most `exp(−2 (c−1)² ε² t)`. Step 4: a union bound over all `|X| · |Y|` inputs shows that the union of the bad events has probability less than one, so some table `ωs` lies outside every bad event. Step 5: for that table, the number of bad indices for each `(x, y)` is less than `c ε t`, which is the claimed fraction bound. -/
theorem CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.exists_good_randomness
    [FiniteProbabilitySpace Ω]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) (c : ℝ)
    (hc : 1 < c)
    (hp : p.ApproxComputes f ε) :
    ∃ (ωs : Fin (derandomizationSamples X Y ε c) → Ω),
      ∀ (x : X) (y : Y),
        ((Finset.univ.filter (fun i => p.rrun x y (ωs i) ≠ f x y)).card : ℝ) /
          (derandomizationSamples X Y ε c)
          ≤ c * ε := by
  haveI : Nonempty Ω := Measure.nonempty_of_neZero (volume : Measure Ω)
  -- Step 1: degenerate cases.
  -- Handle X or Y empty (conclusion is vacuously true)
  by_cases hX : IsEmpty X
  · exact ⟨fun _ => Classical.arbitrary Ω, fun x => hX.elim x⟩
  by_cases hY : IsEmpty Y
  · exact ⟨fun _ => Classical.arbitrary Ω, fun _ y => hY.elim y⟩
  rw [not_isEmpty_iff] at hX hY
  -- Handle ε ≥ 1: any choice works since c * ε ≥ c > 1 ≥ #{bad}/t
  by_cases hε1 : 1 ≤ ε
  · refine ⟨fun _ => Classical.arbitrary Ω, fun x y => ?_⟩
    have ht_pos : (0 : ℝ) < derandomizationSamples X Y ε c :=
      Nat.cast_pos.mpr (by simp [derandomizationSamples])
    have : (((Finset.univ (α := Fin (derandomizationSamples X Y ε c))).filter (fun i =>
        p.rrun x y ((fun _ => Classical.arbitrary Ω) i) ≠ f x y)).card : ℝ) /
        derandomizationSamples X Y ε c ≤ 1 := by
      rw [div_le_one ht_pos]
      simp only [rrun_eq, ne_eq, Finset.filter_const, ite_not]
      exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
    linarith [show (1 : ℝ) ≤ c * ε from by nlinarith]
  push_neg at hε1 -- hε1 : ε < 1
  -- Handle ε < 0: contradiction with ApproxComputes (measure ≥ 0 > ε)
  by_cases hε_neg : ε < 0
  · exfalso
    obtain ⟨x₀⟩ := hX; obtain ⟨y₀⟩ := hY
    linarith [hp x₀ y₀,
      MeasureTheory.measureReal_nonneg (μ := volume) (s := {ω | p.rrun x₀ y₀ ω ≠ f x₀ y₀})]
  push_neg at hε_neg -- hε_neg : 0 ≤ ε
  -- Handle ε = 0: protocol computes f exactly, pick any good ω
  by_cases hε_zero : ε = 0
  · subst hε_zero
    -- Each bad set has measure 0 (measure ≥ 0 and ≤ 0)
    have h_bad_zero : ∀ x y, volume {ω : Ω | p.rrun x y ω ≠ f x y} = 0 := by
      intro x y
      have hreal : volume.real {ω : Ω | p.rrun x y ω ≠ f x y} = 0 :=
        le_antisymm (hp x y) MeasureTheory.measureReal_nonneg
      exact (MeasureTheory.measureReal_eq_zero_iff
        (μ := volume) (s := {ω : Ω | p.rrun x y ω ≠ f x y})).mp hreal
    -- Unfold rrun so we can use h_bad_zero in measure goals
    simp only [PublicCoin.FiniteMessage.Protocol.rrun] at h_bad_zero
    -- Union of bad sets has measure 0, so some ω₀ is good for all (x,y)
    have h_union : volume (⋃ x : X, ⋃ y : Y,
        {ω : Ω | p.run (ω, x) (ω, y) ≠ f x y}) = 0 := by
      apply le_antisymm _ (zero_le)
      calc volume (⋃ x : X, ⋃ y : Y, {ω | p.run (ω, x) (ω, y) ≠ f x y})
          ≤ ∑' x : X, volume (⋃ y : Y, {ω | p.run (ω, x) (ω, y) ≠ f x y}) :=
            measure_iUnion_le _
        _ ≤ ∑' x : X, ∑' y : Y, volume {ω | p.run (ω, x) (ω, y) ≠ f x y} :=
            ENNReal.tsum_le_tsum (fun x => measure_iUnion_le _)
        _ = 0 := by simp_rw [h_bad_zero, tsum_zero]
    have ⟨ω₀, hω₀⟩ : ∃ ω₀ : Ω, ∀ x y, p.run (ω₀, x) (ω₀, y) = f x y := by
      by_contra h; push_neg at h
      have : ⋃ x : X, ⋃ y : Y, {ω : Ω | p.run (ω, x) (ω, y) ≠ f x y} = Set.univ :=
        Set.eq_univ_of_forall (fun ω => by simp only [Set.mem_iUnion, Set.mem_setOf]; exact h ω)
      rw [this, measure_univ] at h_union; exact one_ne_zero h_union
    refine ⟨fun _ => ω₀, fun x y => ?_⟩
    -- All outputs correct, so filter is empty and 0/t ≤ 0
    simp only [mul_zero, PublicCoin.FiniteMessage.Protocol.rrun, hω₀ x y,
      ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty,
      Nat.cast_zero, zero_div, le_refl]
  -- Main case: 0 < ε
  have hε : 0 < ε := lt_of_le_of_ne hε_neg (Ne.symm hε_zero)
  set t := derandomizationSamples X Y ε c with ht_def
  have ht_pos : 0 < t := by simp [ht_def, derandomizationSamples]
  -- Step 2: the key bound: exp(-2*(c-1)²*ε²*t) * |X| * |Y| < 1
  have ht_bound : Real.exp (-2 * (c - 1) ^ 2 * ε ^ 2 * ↑t) *
      (Fintype.card X * Fintype.card Y) < 1 := by
    set N : ℝ := ↑(Fintype.card X) * ↑(Fintype.card Y) with hN_def
    set D : ℝ := 2 * (c - 1) ^ 2 * ε ^ 2 with hD_def
    have hD_pos : 0 < D := by
      rw [hD_def]
      exact mul_pos (mul_pos (by linarith) (sq_pos_of_pos (by linarith))) (sq_pos_of_pos hε)
    suffices h : Real.exp (-D * ↑t) * N < 1 by
      have : -2 * (c - 1) ^ 2 * ε ^ 2 * ↑t = -D * ↑t := by rw [hD_def]; ring
      rwa [this]
    by_cases hN : N ≤ 0
    · nlinarith [Real.exp_pos (-D * ↑t)]
    · push_neg at hN
      have hL_lt : Real.log N / D < ↑t := by
        have h1 : Real.log N / D ≤ ↑⌈Real.log N / D⌉₊ := Nat.le_ceil _
        have h2 : ⌈Real.log N / D⌉₊ < t := by
          simp only [ht_def, derandomizationSamples, hN_def, hD_def]; omega
        linarith [Nat.cast_lt (α := ℝ).mpr h2]
      have hDt : Real.log N < D * ↑t := by
        rw [div_lt_iff₀ hD_pos] at hL_lt; linarith
      calc Real.exp (-D * ↑t) * N
          < Real.exp (-Real.log N) * N := by
            apply mul_lt_mul_of_pos_right _ hN
            exact Real.exp_strictMono (by linarith)
        _ = 1 := by
            rw [Real.exp_neg, Real.exp_log hN, inv_mul_cancel₀ (ne_of_gt hN)]
  -- Step 3: probabilistic existence on the product space Fin t → Ω
  have : ∃ (ωs : Fin t → Ω), ∀ (x : X) (y : Y),
      ((Finset.univ.filter (fun i => p.rrun x y (ωs i) ≠ f x y)).card : ℝ) / t
        ≤ c * ε := by
    -- For each (x,y), define indicator Y_i(ωs) = 1 if p.rrun x y (ωs i) ≠ f x y
    -- On product space (Fin t → Ω), these are independent across i
    -- Apply prob_many_events_le, then union bound
    -- Define the "bad" event for each (x,y)
    set bad : X → Y → Set (Fin t → Ω) :=
      fun x y => {ωs | c * ε * ↑t ≤
        ∑ i : Fin t, if p.rrun x y (ωs i) ≠ f x y then (1 : ℝ) else 0}
    -- Each bad event has small measure by prob_many_events_le
    set μ : Measure (Fin t → Ω) := volume with hμ_def
    have hbad_measure : ∀ x y,
        μ.real (bad x y) ≤
          Real.exp (-2 * (c - 1) ^ 2 * ε ^ 2 * ↑t) := by
      intro x y
      apply prob_many_events_le
        (Y := fun i (ωs : Fin t → Ω) =>
          if p.rrun x y (ωs i) ≠ f x y then (1 : ℝ) else 0)
      · -- Independence
        have hcoord : iIndepFun (fun i (ωs : Fin t → Ω) => ωs i)
            (volume : Measure (Fin t → Ω)) :=
          iIndepFun_pi (fun i => aemeasurable_id)
        exact hcoord.comp
          (fun i (ω : Ω) => if p.rrun x y ω ≠ f x y then (1 : ℝ) else 0)
          (fun i => Measurable.of_discrete)
      · -- Measurability
        intro i
        have : (fun ωs : Fin t → Ω =>
          if p.rrun x y (ωs i) ≠ f x y then (1 : ℝ) else 0) =
          (fun ω : Ω => if p.rrun x y ω ≠ f x y then (1 : ℝ) else 0) ∘
          (fun ωs => ωs i) := rfl
        rw [this]
        exact Measurable.of_discrete.aemeasurable.comp_measurable (measurable_pi_apply i)
      · -- [0,1]-valued
        intro i; exact Filter.Eventually.of_forall
          (fun ωs => Set.mem_Icc.mpr ⟨ite_nonneg zero_le_one le_rfl, ite_le_one le_rfl zero_le_one⟩)
      · -- Mean bound: E[Y_i] = P[p.rrun x y ω ≠ f x y] ≤ ε
        intro i
        -- The i-th coordinate of the product space has the original distribution.
        set g : Ω → ℝ := fun ω => if p.rrun x y ω ≠ f x y then 1 else 0
        have : ∫ ωs, g (ωs i) ∂μ = ∫ ω, g ω ∂(volume : Measure Ω) := by
          simpa [hμ_def] using
            (FiniteProbabilitySpace.integral_comp_eval (ι := Fin t) (Ω := Ω) i g)
        rw [this]
        -- Identify the mean with the failure probability on a single input.
        have hg_eq : g = Set.indicator {ω | p.rrun x y ω ≠ f x y} 1 := by
          ext ω; simp [g, Set.indicator_apply]; split_ifs <;> simp_all
        rw [hg_eq]
        rw [← FiniteProbabilitySpace.measureReal_eq_integral_indicator_one
          (Ω := Ω) {ω | p.rrun x y ω ≠ f x y}]
        exact hp x y
      · linarith
      · exact hc
      · exact ht_pos
    -- Step 4: union bound
    have hunion : μ.real (⋃ x : X, ⋃ y : Y, bad x y) < 1 := by
      calc μ.real (⋃ x : X, ⋃ y : Y, bad x y)
          ≤ ∑ x : X, μ.real (⋃ y : Y, bad x y) :=
            measureReal_iUnion_fintype_le _
        _ ≤ ∑ x : X, ∑ y : Y, μ.real (bad x y) := by
            apply Finset.sum_le_sum; intro x _
            exact measureReal_iUnion_fintype_le _
        _ ≤ ∑ x : X, ∑ _y : Y,
              Real.exp (-2 * (c - 1) ^ 2 * ε ^ 2 * ↑t) := by
            apply Finset.sum_le_sum; intro x _
            exact Finset.sum_le_sum (fun y _ => hbad_measure x y)
        _ = (Fintype.card X * Fintype.card Y) *
              Real.exp (-2 * (c - 1) ^ 2 * ε ^ 2 * ↑t) := by
            simp [Finset.sum_const, mul_comm, mul_assoc]
        _ < 1 := by nlinarith [ht_bound]
    -- Therefore the complement is nonempty: ∃ good ωs
    have hgood : ∃ ωs : Fin t → Ω, ωs ∉ ⋃ x : X, ⋃ y : Y, bad x y := by
      by_contra h
      push_neg at h
      have : ⋃ x : X, ⋃ y : Y, bad x y = Set.univ := Set.eq_univ_of_forall h
      rw [this, probReal_univ] at hunion
      linarith
    obtain ⟨ωs, hωs⟩ := hgood
    refine ⟨ωs, fun x y => ?_⟩
    -- Step 5: ωs is not bad for any (x,y), so #{bad i}/t ≤ c*ε
    simp only [Set.mem_iUnion, not_exists, bad, Set.mem_setOf_eq, not_le] at hωs
    have hlt := hωs x y
    have hsum_eq : ∑ i : Fin t,
        (if p.rrun x y (ωs i) ≠ f x y then (1 : ℝ) else 0) =
        (Finset.univ.filter (fun i => p.rrun x y (ωs i) ≠ f x y)).card := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    rw [hsum_eq] at hlt
    rw [div_le_iff₀ (by exact_mod_cast ht_pos : (0 : ℝ) < ↑t)]
    linarith
  obtain ⟨ωs, hωs⟩ := this
  exact ⟨ωs, hωs⟩
