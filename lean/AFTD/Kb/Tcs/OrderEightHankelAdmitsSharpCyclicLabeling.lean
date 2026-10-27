import AFTD.Prelude
import AFTD.Kb.Tcs.AdmitsSharpCyclicLabeling
import AFTD.Kb.Tcs.IsSharpCyclicLabeling
import AFTD.Kb.Tcs.CyclicMatrixFourier
import AFTD.Kb.Tcs.IsWeightedPartialPermutation

/-!
# order_eight_hankel_admits_sharp_cyclic_labeling

Topic: combinatorics   Node: 1a490e55eb49

Provenance: helper lemma. step towards exists_non_circulant_sharp_cyclic_graph_order_eight

Any simple graph on ZMod 8 whose adjacency is given by (x + y).val ∈ {1, 3, 5} admits a sharp cyclic labeling.
-/

private lemma order_eight_hankel_ph_apply {N : ℕ} [NeZero N] (a : ZMod N) :
    ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) a
      = Complex.exp (-2 * ↑Real.pi * Complex.I * (↑a.val / ↑N)) := by
  rw [AddChar.inv_apply', ZMod.stdAddChar_apply, ZMod.toCircle_apply, ← Complex.exp_neg]
  congr 1; ring

private lemma order_eight_hankel_ph_primitive (N : ℕ) [NeZero N] :
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

private lemma order_eight_hankel_fourier_eq_zero {N : ℕ} [NeZero N] (φ : ZMod N → ℂ) {m n : ZMod N}
    (hmn : m ≠ n) :
    cyclic_matrix_fourier N (Matrix.of fun x y => φ (x + y)) m n = 0 := by
  rw [show cyclic_matrix_fourier N (Matrix.of fun x y => φ (x + y)) m n
       = 1 / (N:ℂ) * ∑ x, ∑ y, φ (x + y)
            * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) (m*x + n*y) from by
        simp only [cyclic_matrix_fourier, Matrix.of_apply]
        congr 1
        apply Finset.sum_congr rfl; intro x _
        apply Finset.sum_congr rfl; intro y _
        rw [order_eight_hankel_ph_apply]]
  have hsplit : ∀ x y : ZMod N, m*x + n*y = n*(x+y) + (m-n)*x := by intro x y; ring
  have hfac : ∀ x y : ZMod N, φ (x+y) * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) (m*x+n*y)
        = (φ (x+y) * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) (n*(x+y)))
          * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) ((m-n)*x) := by
    intro x y; rw [hsplit x y, AddChar.map_add_eq_mul, mul_assoc]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hfac x y))]
  have hchange : ∀ x : ZMod N,
      ∑ y, (φ (x+y) * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) (n*(x+y)))
        = ∑ t, φ t * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) (n*t) := by
    intro x
    exact Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun y => by simp)
  have step : ∀ x : ZMod N,
      (∑ y, (φ (x+y) * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) (n*(x+y)))
        * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) ((m-n)*x))
      = (∑ t, φ t * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) (n*t))
        * ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) ((m-n)*x) := by
    intro x; rw [← Finset.sum_mul]; rw [hchange x]
  rw [Finset.sum_congr rfl (fun x _ => step x)]
  rw [← Finset.mul_sum]
  rw [show (∑ x, ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) ((m-n)*x)) = 0 from by
        rw [show (∑ x : ZMod N, ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) ((m-n)*x))
            = ∑ x, ((ZMod.stdAddChar : AddChar (ZMod N) ℂ)⁻¹) (x*(m-n)) from by
              apply Finset.sum_congr rfl; intro x _; rw [mul_comm]]
        rw [AddChar.sum_mulShift (m-n) (order_eight_hankel_ph_primitive N)]
        simp [sub_ne_zero.mpr hmn]]
  ring

private lemma order_eight_hankel_is_weighted_partial_permutation_of_diag {n : Type*} (M : Matrix n n ℂ)
    (h : ∀ i j, i ≠ j → M i j = 0) : is_weighted_partial_permutation M := by
  constructor
  · intro i j₁ j₂ hj₁ hj₂
    have h1 : i = j₁ := by
      by_contra hc
      exact hj₁ (h i j₁ hc)
    have h2 : i = j₂ := by
      by_contra hc
      exact hj₂ (h i j₂ hc)
    rw [← h1, ← h2]
  · intro j i₁ i₂ hi₁ hi₂
    have h1 : i₁ = j := by
      by_contra hc
      exact hi₁ (h i₁ j hc)
    have h2 : i₂ = j := by
      by_contra hc
      exact hi₂ (h i₂ j hc)
    rw [h1, h2]

/-- Any simple graph on ZMod 8 whose adjacency is given by (x + y).val ∈ {1, 3, 5} admits a sharp cyclic labeling. -/
theorem order_eight_hankel_admits_sharp_cyclic_labeling
    (G : SimpleGraph (ZMod 8)) [DecidableRel G.Adj]
    (hG : ∀ x y : ZMod 8, G.Adj x y ↔ (x + y).val = 1 ∨ (x + y).val = 3 ∨ (x + y).val = 5) :
    admits_sharp_cyclic_labeling 8 G := by
  use Equiv.refl (ZMod 8)
  rw [is_sharp_cyclic_labeling]
  let φ : ZMod 8 → ℂ := fun s => if s.val = 1 ∨ s.val = 3 ∨ s.val = 5 then 1 else 0
  have hM : (Matrix.of fun x y => if G.Adj ((Equiv.refl (ZMod 8)) x) ((Equiv.refl (ZMod 8)) y) then (1 : ℂ) else 0)
          = (Matrix.of fun x y => φ (x + y)) := by
    ext x y
    simp only [Matrix.of_apply]
    change (if G.Adj x y then (1 : ℂ) else 0) = φ (x + y)
    have h_iff := hG x y
    dsimp [φ]
    split_ifs with h1 h2 h3
    · rfl
    · exfalso; exact h2 (h_iff.mp h1)
    · exfalso; exact h1 (h_iff.mpr h3)
    · rfl
  rw [hM]
  apply order_eight_hankel_is_weighted_partial_permutation_of_diag
  intro i j hij
  exact order_eight_hankel_fourier_eq_zero φ hij
