import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BooleanProductBernoulli
import AFTD.Kb.GameTheoryEconomics.BooleanInfluence
import AFTD.Kb.GameTheoryEconomics.BooleanInfluenceLeOne
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.BooleanProductBernoulliIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# discrete_poincare_monotone_boolean

Topic: combinatorial_games   Node: 3aab48232d18

Provenance: formalization of a published result. Source: arXiv:2610.30730 Lemma 2.1

Let $U$ be a finite non-empty type with decidable equality, and let $f : (U \to \mathrm{Bool}) \to \mathrm{Bool}$ be a monotone function. For any parameter $p$ in the unit interval `unitInterval`, the variance of the real indicator `fun x => if f x then 1 else 0` under `boolean_product_bernoulli U p` is at most $(p : \mathbb{R}) * (1 - (p : \mathbb{R})) * \sum_{i : U} \mathrm{boolean\_influence}\ U\ f\ i\ p$.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def discrete_poincare_monotone_boolean_W (p : unitInterval) (b : Bool) : ℝ :=
  if b then (p : ℝ) else 1 - (p : ℝ)

lemma discrete_poincare_monotone_boolean_bernW (p : unitInterval) (b : Bool) :
    (bernoulliMeasure true false p).real {b} = discrete_poincare_monotone_boolean_W p b := by
  cases b
  · rw [discrete_poincare_monotone_boolean_W, if_neg (by simp)]
    exact bernoulliMeasure_real_apply_of_notMem_of_mem p (measurableSet_singleton false) (by simp) (by simp)
  · rw [discrete_poincare_monotone_boolean_W, if_pos rfl]
    exact bernoulliMeasure_real_apply_of_mem_of_notMem p (measurableSet_singleton true) (by simp) (by simp)

lemma discrete_poincare_monotone_boolean_prodReal (U : Type*) [Fintype U] (p : unitInterval)
    (x : U → Bool) :
    (boolean_product_bernoulli U p).real {x} = ∏ i, discrete_poincare_monotone_boolean_W p (x i) := by
  rw [boolean_product_bernoulli, Measure.real_def, Measure.pi_singleton,
    ENNReal.toReal_prod (Finset.univ) (fun i => (bernoulliMeasure true false p) {x i})]
  exact Finset.prod_congr rfl (fun i _ => discrete_poincare_monotone_boolean_bernW p (x i))

lemma discrete_poincare_monotone_boolean_integralFormula (U : Type*) [Fintype U]
    [DecidableEq U] (p : unitInterval) (h : (U → Bool) → ℝ) :
    ∫ x, h x ∂(boolean_product_bernoulli U p)
      = ∑ x, (∏ i, discrete_poincare_monotone_boolean_W p (x i)) * h x := by
  rw [MeasureTheory.integral_fintype (MeasureTheory.Integrable.of_finite)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [discrete_poincare_monotone_boolean_prodReal]
  simp [smul_eq_mul]

noncomputable def discrete_poincare_monotone_boolean_ext (U : Type*) [DecidableEq U] (q : U)
    (y : {a : U // a ≠ q} → Bool) (b : Bool) : U → Bool :=
  fun a => if h : a = q then b else y ⟨a, h⟩

lemma discrete_poincare_monotone_boolean_ext_self (U : Type*) [DecidableEq U] (q : U)
    (y : {a : U // a ≠ q} → Bool) (b : Bool) :
    discrete_poincare_monotone_boolean_ext U q y b q = b := by
  simp [discrete_poincare_monotone_boolean_ext]

lemma discrete_poincare_monotone_boolean_ext_ne (U : Type*) [DecidableEq U] (q : U)
    (y : {a : U // a ≠ q} → Bool) (b : Bool) (a : U) (ha : a ≠ q) :
    discrete_poincare_monotone_boolean_ext U q y b a = y ⟨a, ha⟩ := by
  simp [discrete_poincare_monotone_boolean_ext, ha]

lemma discrete_poincare_monotone_boolean_updQ (U : Type*) [DecidableEq U] (q : U)
    (y : {a : U // a ≠ q} → Bool) (b b' : Bool) :
    Function.update (discrete_poincare_monotone_boolean_ext U q y b) q b'
      = discrete_poincare_monotone_boolean_ext U q y b' := by
  funext a
  by_cases h : a = q
  · rw [h]; simp [Function.update, discrete_poincare_monotone_boolean_ext]
  · simp [Function.update, discrete_poincare_monotone_boolean_ext, h]

lemma discrete_poincare_monotone_boolean_updNe (U : Type*) [DecidableEq U] (q : U)
    (y : {a : U // a ≠ q} → Bool) (b : Bool) (a : U) (ha : a ≠ q) (c : Bool) :
    Function.update (discrete_poincare_monotone_boolean_ext U q y b) a c
      = discrete_poincare_monotone_boolean_ext U q (Function.update y ⟨a, ha⟩ c) b := by
  funext j
  by_cases hq : j = q
  · rw [hq]; simp [Function.update, discrete_poincare_monotone_boolean_ext,
      (show q ≠ a from fun h => ha h.symm)]
  · by_cases haj : j = a
    · rw [haj]; simp [Function.update, discrete_poincare_monotone_boolean_ext, ha]
    · simp [Function.update, discrete_poincare_monotone_boolean_ext, hq, haj]

lemma discrete_poincare_monotone_boolean_monoExt (U : Type*) [DecidableEq U] (q : U) (b : Bool) :
    Monotone (fun y : {a : U // a ≠ q} → Bool =>
      discrete_poincare_monotone_boolean_ext U q y b) := by
  intro y y' hy a
  change discrete_poincare_monotone_boolean_ext U q y b a
    ≤ discrete_poincare_monotone_boolean_ext U q y' b a
  by_cases h : a = q
  · rw [h]; simp [discrete_poincare_monotone_boolean_ext_self]
  · rw [discrete_poincare_monotone_boolean_ext_ne U q y b a h,
      discrete_poincare_monotone_boolean_ext_ne U q y' b a h]
    exact hy ⟨a, h⟩

noncomputable def discrete_poincare_monotone_boolean_split (U : Type*) [DecidableEq U] (q : U) :
    (U → Bool) ≃ ({a : U // a ≠ q} → Bool) × Bool where
  toFun x := (fun a => x a.1, x q)
  invFun yb := discrete_poincare_monotone_boolean_ext U q yb.1 yb.2
  left_inv x := by
    funext a
    by_cases h : a = q
    · subst h; simp [discrete_poincare_monotone_boolean_ext]
    · simp [discrete_poincare_monotone_boolean_ext, h]
  right_inv yb := by
    obtain ⟨y, b⟩ := yb
    simp only [Prod.mk.injEq]
    exact ⟨funext (fun a => discrete_poincare_monotone_boolean_ext_ne U q y b a.1 a.2),
      discrete_poincare_monotone_boolean_ext_self U q y b⟩

@[simp] lemma discrete_poincare_monotone_boolean_splitSymm (U : Type*) [DecidableEq U] (q : U)
    (y : {a : U // a ≠ q} → Bool) (b : Bool) :
    (discrete_poincare_monotone_boolean_split U q).symm (y, b)
      = discrete_poincare_monotone_boolean_ext U q y b := rfl

lemma discrete_poincare_monotone_boolean_weightSplit (U : Type*) [Fintype U] [DecidableEq U]
    (q : U) (p : unitInterval) (y : {a : U // a ≠ q} → Bool) (b : Bool) :
    (∏ i : U, discrete_poincare_monotone_boolean_W p
        (discrete_poincare_monotone_boolean_ext U q y b i))
      = (∏ a : {a : U // a ≠ q}, discrete_poincare_monotone_boolean_W p (y a))
        * discrete_poincare_monotone_boolean_W p b := by
  rw [← Finset.mul_prod_erase Finset.univ
    (fun i => discrete_poincare_monotone_boolean_W p
      (discrete_poincare_monotone_boolean_ext U q y b i)) (Finset.mem_univ q)]
  rw [discrete_poincare_monotone_boolean_ext_self, mul_comm]
  congr 1
  rw [Finset.prod_subtype (p := fun a => a ≠ q) (s := Finset.univ.erase q) (by intro x; simp)]
  exact Finset.prod_congr rfl (fun a _ =>
    by rw [discrete_poincare_monotone_boolean_ext_ne U q y b a.1 a.2])

lemma discrete_poincare_monotone_boolean_sumSplit (U : Type*) [Fintype U] [DecidableEq U]
    (q : U) (p : unitInterval) (h : (U → Bool) → ℝ) :
    ∑ x : U → Bool, (∏ i, discrete_poincare_monotone_boolean_W p (x i)) * h x
      = ∑ y : {a : U // a ≠ q} → Bool,
          (∏ a, discrete_poincare_monotone_boolean_W p (y a)) *
            ((1 - (p:ℝ)) * h (discrete_poincare_monotone_boolean_ext U q y false)
              + (p:ℝ) * h (discrete_poincare_monotone_boolean_ext U q y true)) := by
  rw [← Equiv.sum_comp (discrete_poincare_monotone_boolean_split U q).symm
    (fun x => (∏ i, discrete_poincare_monotone_boolean_W p (x i)) * h x)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Fintype.sum_bool]
  simp only [discrete_poincare_monotone_boolean_splitSymm]
  rw [discrete_poincare_monotone_boolean_weightSplit U q p y false,
    discrete_poincare_monotone_boolean_weightSplit U q p y true]
  simp only [discrete_poincare_monotone_boolean_W, Bool.false_eq_true, if_false, if_true]
  ring

lemma discrete_poincare_monotone_boolean_integralSplit (U : Type*) [Fintype U] [DecidableEq U]
    (q : U) (p : unitInterval) (h : (U → Bool) → ℝ) :
    ∫ x, h x ∂(boolean_product_bernoulli U p)
      = (1 - (p:ℝ)) * ∫ y, h (discrete_poincare_monotone_boolean_ext U q y false)
          ∂(boolean_product_bernoulli {a : U // a ≠ q} p)
        + (p:ℝ) * ∫ y, h (discrete_poincare_monotone_boolean_ext U q y true)
          ∂(boolean_product_bernoulli {a : U // a ≠ q} p) := by
  rw [discrete_poincare_monotone_boolean_integralFormula U p h,
    discrete_poincare_monotone_boolean_integralFormula {a : U // a ≠ q} p
      (fun y => h (discrete_poincare_monotone_boolean_ext U q y false)),
    discrete_poincare_monotone_boolean_integralFormula {a : U // a ≠ q} p
      (fun y => h (discrete_poincare_monotone_boolean_ext U q y true)),
    discrete_poincare_monotone_boolean_sumSplit U q p h, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun y _ => by ring)

noncomputable def discrete_poincare_monotone_boolean_mean (U : Type*) [Fintype U]
    (f : (U → Bool) → Bool) (p : unitInterval) : ℝ :=
  ∫ x, (if f x then (1:ℝ) else 0) ∂(boolean_product_bernoulli U p)

lemma discrete_poincare_monotone_boolean_varianceEq (U : Type*) [Fintype U] [DecidableEq U]
    (f : (U → Bool) → Bool) (p : unitInterval) :
    ProbabilityTheory.variance (fun x => if f x then (1:ℝ) else 0) (boolean_product_bernoulli U p)
      = discrete_poincare_monotone_boolean_mean U f p
        * (1 - discrete_poincare_monotone_boolean_mean U f p) := by
  have hmeas : AEMeasurable (fun x : U → Bool => if f x then (1:ℝ) else 0)
      (boolean_product_bernoulli U p) := (measurable_of_finite _).aemeasurable
  have hae : ∀ᵐ ω ∂(boolean_product_bernoulli U p),
      (if f ω then (1:ℝ) else 0) = 0 ∨ (if f ω then (1:ℝ) else 0) = 1 := by
    filter_upwards with ω; by_cases h : f ω <;> simp [h]
  have h1 : discrete_poincare_monotone_boolean_mean U f p
      = (boolean_product_bernoulli U p).real
        {ω : U → Bool | (if f ω then (1:ℝ) else 0) = 1} :=
    integral_of_ae_eq_zero_or_one hmeas hae
  have h0 : (boolean_product_bernoulli U p).real
        {ω : U → Bool | (if f ω then (1:ℝ) else 0) = 0}
      = ∫ x, 1 - (if f x then (1:ℝ) else 0) ∂(boolean_product_bernoulli U p) :=
    (integral_one_sub_of_ae_eq_zero_or_one hmeas hae).symm
  have hsub : ∫ x, 1 - (if f x then (1:ℝ) else 0) ∂(boolean_product_bernoulli U p)
      = 1 - discrete_poincare_monotone_boolean_mean U f p := by
    rw [integral_sub]
    · rw [integral_const, discrete_poincare_monotone_boolean_mean]; simp [Measure.real, smul_eq_mul]
    · exact Integrable.of_finite
    · exact Integrable.of_finite
  rw [variance_of_ae_eq_zero_or_one hmeas hae, ← h1, h0, hsub]
  ring

lemma discrete_poincare_monotone_boolean_intUpdQ (U : Type*) [Fintype U] [DecidableEq U]
    (q : U) (p : unitInterval) (f : (U → Bool) → Bool) (c : Bool) :
    ∫ x, (if f (Function.update x q c) then (1:ℝ) else 0) ∂(boolean_product_bernoulli U p)
      = ∫ y, (if f (discrete_poincare_monotone_boolean_ext U q y c) then (1:ℝ) else 0)
          ∂(boolean_product_bernoulli {a : U // a ≠ q} p) := by
  rw [discrete_poincare_monotone_boolean_integralSplit U q p
    (fun x => if f (Function.update x q c) then (1:ℝ) else 0)]
  have e1 : (fun y : {a : U // a ≠ q} → Bool =>
      (if f (Function.update (discrete_poincare_monotone_boolean_ext U q y false) q c)
        then (1:ℝ) else 0))
      = (fun y => (if f (discrete_poincare_monotone_boolean_ext U q y c) then (1:ℝ) else 0)) := by
    funext y; rw [discrete_poincare_monotone_boolean_updQ]
  have e2 : (fun y : {a : U // a ≠ q} → Bool =>
      (if f (Function.update (discrete_poincare_monotone_boolean_ext U q y true) q c)
        then (1:ℝ) else 0))
      = (fun y => (if f (discrete_poincare_monotone_boolean_ext U q y c) then (1:ℝ) else 0)) := by
    funext y; rw [discrete_poincare_monotone_boolean_updQ]
  rw [e1, e2, ← add_mul]
  have : (1 - (p:ℝ)) + (p:ℝ) = 1 := by ring
  rw [this, one_mul]

lemma discrete_poincare_monotone_boolean_intUpdNe (U : Type*) [Fintype U] [DecidableEq U]
    (q : U) (p : unitInterval) (f : (U → Bool) → Bool) (a : U) (ha : a ≠ q) (c : Bool) :
    ∫ x, (if f (Function.update x a c) then (1:ℝ) else 0) ∂(boolean_product_bernoulli U p)
      = (1 - (p:ℝ)) * ∫ y, (if f (discrete_poincare_monotone_boolean_ext U q
            (Function.update y ⟨a, ha⟩ c) false) then (1:ℝ) else 0)
            ∂(boolean_product_bernoulli {b : U // b ≠ q} p)
        + (p:ℝ) * ∫ y, (if f (discrete_poincare_monotone_boolean_ext U q
            (Function.update y ⟨a, ha⟩ c) true) then (1:ℝ) else 0)
            ∂(boolean_product_bernoulli {b : U // b ≠ q} p) := by
  rw [discrete_poincare_monotone_boolean_integralSplit U q p
    (fun x => if f (Function.update x a c) then (1:ℝ) else 0)]
  have e1 : (fun y : {b : U // b ≠ q} → Bool =>
      (if f (Function.update (discrete_poincare_monotone_boolean_ext U q y false) a c)
        then (1:ℝ) else 0))
      = (fun y => (if f (discrete_poincare_monotone_boolean_ext U q
          (Function.update y ⟨a, ha⟩ c) false) then (1:ℝ) else 0)) := by
    funext y; rw [discrete_poincare_monotone_boolean_updNe]
  have e2 : (fun y : {b : U // b ≠ q} → Bool =>
      (if f (Function.update (discrete_poincare_monotone_boolean_ext U q y true) a c)
        then (1:ℝ) else 0))
      = (fun y => (if f (discrete_poincare_monotone_boolean_ext U q
          (Function.update y ⟨a, ha⟩ c) true) then (1:ℝ) else 0)) := by
    funext y; rw [discrete_poincare_monotone_boolean_updNe]
  rw [e1, e2]

noncomputable def discrete_poincare_monotone_boolean_S (U : Type*) [Fintype U] [DecidableEq U]
    (f : (U → Bool) → Bool) (i : U) (c : Bool) (p : unitInterval) : ℝ :=
  ∫ x, (if f (Function.update x i c) then (1 : ℝ) else 0) ∂(boolean_product_bernoulli U p)

lemma discrete_poincare_monotone_boolean_infSub (U : Type*) [Fintype U] [DecidableEq U]
    (f : (U → Bool) → Bool) (i : U) (p : unitInterval) :
    boolean_influence U f i p = discrete_poincare_monotone_boolean_S U f i true p
      - discrete_poincare_monotone_boolean_S U f i false p := by
  simp only [boolean_influence, discrete_poincare_monotone_boolean_S]
  exact integral_sub Integrable.of_finite Integrable.of_finite

lemma discrete_poincare_monotone_boolean_infSplitQ (U : Type*) [Fintype U] [DecidableEq U]
    (q : U) (p : unitInterval) (f : (U → Bool) → Bool) :
    boolean_influence U f q p
      = discrete_poincare_monotone_boolean_mean {b : U // b ≠ q}
          (fun y => f (discrete_poincare_monotone_boolean_ext U q y true)) p
        - discrete_poincare_monotone_boolean_mean {b : U // b ≠ q}
          (fun y => f (discrete_poincare_monotone_boolean_ext U q y false)) p := by
  rw [discrete_poincare_monotone_boolean_infSub]
  have h1 : discrete_poincare_monotone_boolean_S U f q true p
      = discrete_poincare_monotone_boolean_mean {b : U // b ≠ q}
          (fun y => f (discrete_poincare_monotone_boolean_ext U q y true)) p :=
    discrete_poincare_monotone_boolean_intUpdQ U q p f true
  have h2 : discrete_poincare_monotone_boolean_S U f q false p
      = discrete_poincare_monotone_boolean_mean {b : U // b ≠ q}
          (fun y => f (discrete_poincare_monotone_boolean_ext U q y false)) p :=
    discrete_poincare_monotone_boolean_intUpdQ U q p f false
  rw [h1, h2]

lemma discrete_poincare_monotone_boolean_infSplit (U : Type*) [Fintype U] [DecidableEq U]
    (q : U) (p : unitInterval) (f : (U → Bool) → Bool) (a : U) (ha : a ≠ q) :
    boolean_influence U f a p
      = (1 - (p:ℝ)) * boolean_influence {b : U // b ≠ q}
          (fun y => f (discrete_poincare_monotone_boolean_ext U q y false)) ⟨a, ha⟩ p
        + (p:ℝ) * boolean_influence {b : U // b ≠ q}
          (fun y => f (discrete_poincare_monotone_boolean_ext U q y true)) ⟨a, ha⟩ p := by
  rw [discrete_poincare_monotone_boolean_infSub,
    discrete_poincare_monotone_boolean_infSub,
    discrete_poincare_monotone_boolean_infSub]
  have e1 := discrete_poincare_monotone_boolean_intUpdNe U q p f a ha true
  have e2 := discrete_poincare_monotone_boolean_intUpdNe U q p f a ha false
  simp only [discrete_poincare_monotone_boolean_S]
  rw [e1, e2]
  ring

lemma discrete_poincare_monotone_boolean_meanSplit (U : Type*) [Fintype U] [DecidableEq U]
    (q : U) (p : unitInterval) (f : (U → Bool) → Bool) :
    discrete_poincare_monotone_boolean_mean U f p
      = (1 - (p:ℝ)) * discrete_poincare_monotone_boolean_mean {b : U // b ≠ q}
          (fun y => f (discrete_poincare_monotone_boolean_ext U q y false)) p
        + (p:ℝ) * discrete_poincare_monotone_boolean_mean {b : U // b ≠ q}
          (fun y => f (discrete_poincare_monotone_boolean_ext U q y true)) p :=
  discrete_poincare_monotone_boolean_integralSplit U q p (fun x => if f x then (1:ℝ) else 0)

lemma discrete_poincare_monotone_boolean_meanBounds (U : Type*) [Fintype U] [DecidableEq U]
    (f : (U → Bool) → Bool) (p : unitInterval) :
    0 ≤ discrete_poincare_monotone_boolean_mean U f p ∧
      discrete_poincare_monotone_boolean_mean U f p ≤ 1 := by
  constructor
  · exact integral_nonneg (fun x => by by_cases h : f x <;> simp [h])
  · have h2 : ∫ x, (if f x then (1:ℝ) else 0) ∂(boolean_product_bernoulli U p)
        ≤ ∫ _x : U → Bool, (1:ℝ) ∂(boolean_product_bernoulli U p) := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro x; by_cases h : f x <;> simp [h]
    rw [show discrete_poincare_monotone_boolean_mean U f p
      = ∫ x, (if f x then (1:ℝ) else 0) ∂(boolean_product_bernoulli U p) from rfl]
    rwa [show (∫ _x : U → Bool, (1:ℝ) ∂(boolean_product_bernoulli U p)) = 1 by
      rw [integral_const]; simp] at h2

lemma discrete_poincare_monotone_boolean_boolLe : ∀ a b : Bool, a ≤ b →
    (if a then (1:ℝ) else 0) ≤ (if b then (1:ℝ) else 0) := by
  intro a b hab
  match a, b, hab with
  | true, true, _ => simp
  | false, true, _ => simp
  | false, false, _ => simp
  | true, false, h => exact absurd h (by decide)

lemma discrete_poincare_monotone_boolean_meanMono (U : Type*) [Fintype U] [DecidableEq U]
    (q : U) (p : unitInterval) (f : (U → Bool) → Bool) (hf : Monotone f) :
    discrete_poincare_monotone_boolean_mean {b : U // b ≠ q}
        (fun y => f (discrete_poincare_monotone_boolean_ext U q y false)) p
      ≤ discrete_poincare_monotone_boolean_mean {b : U // b ≠ q}
        (fun y => f (discrete_poincare_monotone_boolean_ext U q y true)) p := by
  apply integral_mono Integrable.of_finite Integrable.of_finite
  intro y
  have hle : discrete_poincare_monotone_boolean_ext U q y false
      ≤ discrete_poincare_monotone_boolean_ext U q y true := by
    intro a
    by_cases h : a = q
    · rw [h]; simp [discrete_poincare_monotone_boolean_ext_self]
    · rw [discrete_poincare_monotone_boolean_ext_ne U q y false a h,
        discrete_poincare_monotone_boolean_ext_ne U q y true a h]
  exact discrete_poincare_monotone_boolean_boolLe _ _ (hf hle)

lemma discrete_poincare_monotone_boolean_keyIneq (p m0 m1 S0 S1 : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hm0 : 0 ≤ m0) (hm01 : m0 ≤ m1) (hm1 : m1 ≤ 1)
    (h0 : m0 * (1 - m0) ≤ p * (1 - p) * S0)
    (h1 : m1 * (1 - m1) ≤ p * (1 - p) * S1) :
    ((1 - p) * m0 + p * m1) * (1 - ((1 - p) * m0 + p * m1))
      ≤ p * (1 - p) * ((m1 - m0) + ((1 - p) * S0 + p * S1)) := by
  have hq : (0:ℝ) ≤ 1 - p := by linarith
  have hpq : (0:ℝ) ≤ p * (1 - p) := mul_nonneg hp0 hq
  have hx0 : (0:ℝ) ≤ m1 - m0 := by linarith
  have hx1 : m1 - m0 ≤ 1 := by linarith
  have hC : p * (1 - p) * (m1 - m0) ^ 2 ≤ p * (1 - p) * (m1 - m0) := by
    have := mul_nonneg hpq (mul_nonneg hx0 (by linarith : (0:ℝ) ≤ 1 - (m1 - m0)))
    nlinarith
  have hA := mul_le_mul_of_nonneg_left h0 hq
  have hB := mul_le_mul_of_nonneg_left h1 hp0
  nlinarith [hA, hB, hC]

lemma discrete_poincare_monotone_boolean_aux : ∀ (n : ℕ) (U : Type*) [Fintype U] [DecidableEq U],
    Fintype.card U = n → ∀ (f : (U → Bool) → Bool), Monotone f → ∀ p : unitInterval,
    ProbabilityTheory.variance (fun x => if f x then (1 : ℝ) else 0) (boolean_product_bernoulli U p)
      ≤ (p : ℝ) * (1 - (p : ℝ)) * ∑ i : U, boolean_influence U f i p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U instF instD hcard f hf p
    rcases Nat.eq_zero_or_pos n with hn | hn
    · have hise : IsEmpty U := Fintype.card_eq_zero_iff.mp (hcard.trans hn)
      letI := hise
      have hX : (fun x : U → Bool => (if f x then (1:ℝ) else 0))
          = fun _ => (if f (fun a => isEmptyElim a) then (1:ℝ) else 0) := by
        funext x
        rw [Subsingleton.elim x (fun a => isEmptyElim a)]
      rw [discrete_poincare_monotone_boolean_varianceEq]
      have hm : discrete_poincare_monotone_boolean_mean U f p
          = (if f (fun a => isEmptyElim a) then (1:ℝ) else 0) := by
        have h2 : discrete_poincare_monotone_boolean_mean U f p
            = ∫ x, (if f (fun a => isEmptyElim a) then (1:ℝ) else 0)
              ∂(boolean_product_bernoulli U p) := by
          simp only [discrete_poincare_monotone_boolean_mean]; rw [hX]
        rw [h2, integral_const]; simp
      rw [hm]
      have hsum0 : (∑ i : U, boolean_influence U f i p) = 0 := by
        rw [Finset.univ_eq_empty]; simp
      rw [hsum0]
      by_cases hc : f (fun a => isEmptyElim a) <;> simp [hc]
    · obtain ⟨q⟩ : Nonempty U := Fintype.card_pos_iff.mp (by rw [hcard]; exact hn)
      have hcardV : Fintype.card {b : U // b ≠ q} < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (p := fun b => b ≠ q) (x := q) (by simp)
      have ih0 := ih (Fintype.card {b : U // b ≠ q}) hcardV {b : U // b ≠ q} rfl
        (fun y => f (discrete_poincare_monotone_boolean_ext U q y false))
        (hf.comp (discrete_poincare_monotone_boolean_monoExt U q false)) p
      rw [discrete_poincare_monotone_boolean_varianceEq] at ih0
      have ih1 := ih (Fintype.card {b : U // b ≠ q}) hcardV {b : U // b ≠ q} rfl
        (fun y => f (discrete_poincare_monotone_boolean_ext U q y true))
        (hf.comp (discrete_poincare_monotone_boolean_monoExt U q true)) p
      rw [discrete_poincare_monotone_boolean_varianceEq] at ih1
      have hb0 := discrete_poincare_monotone_boolean_meanBounds {b : U // b ≠ q}
        (fun y => f (discrete_poincare_monotone_boolean_ext U q y false)) p
      have hb1 := discrete_poincare_monotone_boolean_meanBounds {b : U // b ≠ q}
        (fun y => f (discrete_poincare_monotone_boolean_ext U q y true)) p
      have hmono := discrete_poincare_monotone_boolean_meanMono U q p f hf
      have hVsum : (∑ i : {b : U // b ≠ q}, boolean_influence U f i.1 p)
          = (1 - (p:ℝ)) * (∑ i : {b : U // b ≠ q}, boolean_influence {b : U // b ≠ q}
                (fun y => f (discrete_poincare_monotone_boolean_ext U q y false)) i p)
            + (p:ℝ) * (∑ i : {b : U // b ≠ q}, boolean_influence {b : U // b ≠ q}
                (fun y => f (discrete_poincare_monotone_boolean_ext U q y true)) i p) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ =>
          discrete_poincare_monotone_boolean_infSplit U q p f i.1 i.2)
      have hinfl : (∑ i : U, boolean_influence U f i p)
          = (discrete_poincare_monotone_boolean_mean {b : U // b ≠ q}
                (fun y => f (discrete_poincare_monotone_boolean_ext U q y true)) p
              - discrete_poincare_monotone_boolean_mean {b : U // b ≠ q}
                (fun y => f (discrete_poincare_monotone_boolean_ext U q y false)) p)
            + ((1 - (p:ℝ)) * (∑ i : {b : U // b ≠ q}, boolean_influence {b : U // b ≠ q}
                  (fun y => f (discrete_poincare_monotone_boolean_ext U q y false)) i p)
              + (p:ℝ) * (∑ i : {b : U // b ≠ q}, boolean_influence {b : U // b ≠ q}
                  (fun y => f (discrete_poincare_monotone_boolean_ext U q y true)) i p)) := by
        have hsplit : (∑ i : U, boolean_influence U f i p)
            = boolean_influence U f q p
              + ∑ i : {b : U // b ≠ q}, boolean_influence U f i.1 p := by
          rw [← Finset.add_sum_erase Finset.univ (fun i => boolean_influence U f i p)
            (Finset.mem_univ q)]
          congr 1
          rw [Finset.sum_subtype (p := fun b => b ≠ q) (s := Finset.univ.erase q)
            (by intro x; simp)]
        rw [hsplit, discrete_poincare_monotone_boolean_infSplitQ U q p f, hVsum]
      have hmean := discrete_poincare_monotone_boolean_meanSplit U q p f
      rw [discrete_poincare_monotone_boolean_varianceEq, hmean, hinfl]
      exact discrete_poincare_monotone_boolean_keyIneq (p:ℝ) _ _ _ _
        p.2.1 p.2.2 hb0.1 hmono hb1.2 ih0 ih1

/-- Discrete Poincare inequality for monotone Boolean functions under the product Bernoulli measure. -/
theorem discrete_poincare_monotone_boolean (U : Type*) [Fintype U] [Nonempty U] [DecidableEq U]
    (f : (U → Bool) → Bool) (hf : Monotone f) (p : unitInterval) :
    ProbabilityTheory.variance (fun x ↦ if f x then (1 : ℝ) else 0) (boolean_product_bernoulli U p) ≤
      (p : ℝ) * (1 - (p : ℝ)) * ∑ i : U, boolean_influence U f i p := discrete_poincare_monotone_boolean_aux (Fintype.card U) U rfl f hf p
