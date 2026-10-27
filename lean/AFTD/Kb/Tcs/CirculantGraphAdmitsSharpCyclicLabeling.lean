import AFTD.Prelude
import AFTD.Kb.Tcs.AdmitsSharpCyclicLabeling
import AFTD.Kb.Tcs.IsSharpCyclicLabeling
import AFTD.Kb.Tcs.CyclicMatrixFourier
import AFTD.Kb.Tcs.IsWeightedPartialPermutation

/-!
# circulant_graph_admits_sharp_cyclic_labeling

Topic: combinatorics   Node: 8218c2f37e99

Provenance: formalization of a published result. Source: arXiv:2610.31807 Theorem 4.6 and Proposition 8.3

For every N ≥ 1 and every subset s of ZMod N, if the circulant graph SimpleGraph.circulantGraph s has at least one edge, then it admits a sharp cyclic labeling on ZMod N.
-/

open scoped BigOperators

private lemma circulant_graph_admits_sharp_cyclic_labeling_ph_apply {N : ℕ} [NeZero N] (a : ZMod N) :
    ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) a
      = Complex.exp (-2 * ↑Real.pi * Complex.I * (↑a.val / ↑N)) := by
  rw [AddChar.inv_apply', ZMod.stdAddChar_apply, ZMod.toCircle_apply, ← Complex.exp_neg]
  congr 1; ring

private lemma circulant_graph_admits_sharp_cyclic_labeling_ph_primitive (N : ℕ) [NeZero N] :
    ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹).IsPrimitive := by
  intro a ha h
  have h1 : ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) a = 1 := by
    have := congrFun (congrArg DFunLike.coe h) 1
    simpa [AddChar.mulShift] using this
  rw [AddChar.inv_apply'] at h1
  have h2 : ZMod.stdAddChar (N := N) a = 1 := by
    have := congrArg (fun z => z⁻¹) h1; simpa using this
  have h0 : ZMod.stdAddChar (N := N) 0 = 1 := by simp
  rw [← h0] at h2
  exact ha (ZMod.injective_stdAddChar h2)

private lemma circulant_graph_admits_sharp_cyclic_labeling_fourier_eq_zero {N : ℕ} [NeZero N] (φ : ZMod N → ℂ) {m n : ZMod N}
    (hmn : m + n ≠ 0) :
    cyclic_matrix_fourier N (Matrix.of fun x y => φ (x - y)) m n = 0 := by
  rw [show cyclic_matrix_fourier N (Matrix.of fun x y => φ (x - y)) m n
       = 1 / (N:ℂ) * ∑ x, ∑ y, φ (x - y)
            * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) (m*x + n*y) from by
        simp only [cyclic_matrix_fourier, Matrix.of_apply]
        congr 1
        apply Finset.sum_congr rfl; intro x _
        apply Finset.sum_congr rfl; intro y _
        rw [circulant_graph_admits_sharp_cyclic_labeling_ph_apply]]
  have hsplit : ∀ x y : ZMod N, m*x + n*y = -n*(x-y) + (m+n)*x := by intro x y; ring
  have hfac : ∀ x y : ZMod N, φ (x-y) * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) (m*x+n*y)
        = (φ (x-y) * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) (-n*(x-y)))
          * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) ((m+n)*x) := by
    intro x y; rw [hsplit x y, AddChar.map_add_eq_mul, mul_assoc]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hfac x y))]
  have hchange : ∀ x : ZMod N,
      ∑ y, (φ (x-y) * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) (-n*(x-y)))
        = ∑ t, φ t * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) (-n*t) := by
    intro x
    exact Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun y => by simp)
  have step : ∀ x : ZMod N,
      (∑ y, (φ (x-y) * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) (-n*(x-y)))
        * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) ((m+n)*x))
      = (∑ t, φ t * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) (-n*t))
        * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) ((m+n)*x) := by
    intro x; rw [← Finset.sum_mul]; rw [hchange x]
  rw [Finset.sum_congr rfl (fun x _ => step x)]
  rw [← Finset.mul_sum]
  rw [show (∑ x, ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) ((m+n)*x)) = 0 from by
        rw [show (∑ x : ZMod N, ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) ((m+n)*x))
            = ∑ x, ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) (x*(m+n)) from by
              apply Finset.sum_congr rfl; intro x _; rw [mul_comm]]
        rw [AddChar.sum_mulShift (m+n) (circulant_graph_admits_sharp_cyclic_labeling_ph_primitive N)]
        simp [hmn]]
  ring

/-- Every circulant graph with at least one edge admits a sharp cyclic labeling. -/
theorem circulant_graph_admits_sharp_cyclic_labeling (N : ℕ) [NeZero N]
    (s : Set (ZMod N)) [DecidablePred (· ∈ s)]
    (he : ∃ u v, (SimpleGraph.circulantGraph s).Adj u v) :
    admits_sharp_cyclic_labeling N (SimpleGraph.circulantGraph s) := by
  have _ := he
  use Equiv.refl (ZMod N)
  rw [is_sharp_cyclic_labeling]
  let φ : ZMod N → ℂ := fun z => if (z ≠ 0 ∧ (z ∈ s ∨ -z ∈ s)) then 1 else 0
  have hM : (Matrix.of fun x y => if (SimpleGraph.circulantGraph s).Adj ((Equiv.refl (ZMod N)) x) ((Equiv.refl (ZMod N)) y) then (1 : ℂ) else 0)
          = (Matrix.of fun x y => φ (x - y)) := by
    ext x y
    simp only [Matrix.of_apply]
    change (if (SimpleGraph.circulantGraph s).Adj x y then (1 : ℂ) else 0) = φ (x - y)
    have h_iff : (SimpleGraph.circulantGraph s).Adj x y ↔ (x - y ≠ 0 ∧ (x - y ∈ s ∨ -(x - y) ∈ s)) := by
      change (x ≠ y ∧ (x - y ∈ s ∨ y - x ∈ s)) ↔ (x - y ≠ 0 ∧ (x - y ∈ s ∨ -(x - y) ∈ s))
      have h1 : x ≠ y ↔ x - y ≠ 0 := by rw [ne_eq, sub_ne_zero]
      have h2 : y - x = -(x - y) := by ring
      rw [h1, h2]
    dsimp [φ]
    split_ifs with h1 h2 h3
    · rfl
    · exfalso; exact h2 (h_iff.mp h1)
    · exfalso; exact h1 (h_iff.mpr h3)
    · rfl
  rw [hM]
  dsimp [is_weighted_partial_permutation]
  constructor
  · intros i j₁ j₂ hj₁ hj₂
    have h1 : i + j₁ = 0 := by
      by_contra hc
      have hz := circulant_graph_admits_sharp_cyclic_labeling_fourier_eq_zero φ hc
      exact hj₁ hz
    have h2 : i + j₂ = 0 := by
      by_contra hc
      have hz := circulant_graph_admits_sharp_cyclic_labeling_fourier_eq_zero φ hc
      exact hj₂ hz
    have ej₁ := eq_neg_of_add_eq_zero_right h1
    have ej₂ := eq_neg_of_add_eq_zero_right h2
    rw [ej₁, ej₂]
  · intros j i₁ i₂ hi₁ hi₂
    have h1 : i₁ + j = 0 := by
      by_contra hc
      have hz := circulant_graph_admits_sharp_cyclic_labeling_fourier_eq_zero φ hc
      exact hi₁ hz
    have h2 : i₂ + j = 0 := by
      by_contra hc
      have hz := circulant_graph_admits_sharp_cyclic_labeling_fourier_eq_zero φ hc
      exact hi₂ hz
    have ei₁ := eq_neg_of_add_eq_zero_left h1
    have ei₂ := eq_neg_of_add_eq_zero_left h2
    rw [ei₁, ei₂]
