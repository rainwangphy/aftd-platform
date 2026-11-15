import AFTD.Prelude
import AFTD.Kb.Tcs.OseUniversalExtensionOfIsometryExtension
import AFTD.Kb.Tcs.OseTwoLayerCubeExactExtensionThreshold

/-!
# ose_two_layer_cube_universal_extension_threshold

Topic: algorithms   Node: 885b67421197

Provenance: helper lemma. arXiv:2611.08546, Section 6.2; exact-extension threshold and Hilbert extension theorem

For n at least one and positive r,s with s²+2rs=1, consider any two-layer Boolean-cube metric whose first-layer distances are the Euclidean cube distances, whose squared cross distances are r² plus squared cube distances, and whose second-layer cube edges have length s. For every real D, every nonexpanding map from the first layer into any real Hilbert space extends to a D-Lipschitz map on the whole two-layer metric if and only if D≥max(1,sqrt(n)/(2r+s sqrt(n))).
-/

theorem ose_two_layer_cube_universal_extension_threshold (n : ℕ) (hn : 1 ≤ n) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hid : s^2+2*r*s=1)
    (M : MetricSpace (Bool × (Fin n → Bool))) : letI := M
    (∀ (x y : Fin n → Bool), dist (false,x) (false,y) =
      dist (WithLp.toLp 2 (fun i : Fin n => if x i then (1 : ℝ) else 0) : EuclideanSpace ℝ (Fin n))
        (WithLp.toLp 2 (fun i : Fin n => if y i then (1 : ℝ) else 0))) →
    (∀ (x y : Fin n → Bool), dist (false,x) (true,y)^2 = r^2 +
      dist (WithLp.toLp 2 (fun i : Fin n => if x i then (1 : ℝ) else 0) : EuclideanSpace ℝ (Fin n))
        (WithLp.toLp 2 (fun i : Fin n => if y i then (1 : ℝ) else 0))^2) →
    (∀ (x : Fin n → Bool) (i : Fin n), dist (true,x) (true,Function.update x i (!(x i))) = s) →
    ∀ D : ℝ,
      (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (g : (Fin n → Bool) → H),
        (∀ x y, dist (g x) (g y) ≤
          dist (WithLp.toLp 2 (fun i : Fin n => if x i then (1 : ℝ) else 0) : EuclideanSpace ℝ (Fin n))
            (WithLp.toLp 2 (fun i : Fin n => if y i then (1 : ℝ) else 0))) →
        ∃ F : (Bool × (Fin n → Bool)) → H, (∀ x, F (false,x)=g x) ∧
          ∀ a b, dist (F a) (F b) ≤ D*dist a b) ↔
      max 1 (Real.sqrt (n : ℝ)/(2*r+s*Real.sqrt (n : ℝ))) ≤ D := by
  intro hf hc he D
  let U : (Fin n → Bool) → EuclideanSpace ℝ (Fin n) :=
    fun x => WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else 0)
  have hexact := ose_two_layer_cube_exact_extension_threshold n hn r s hr hs hid M hf hc he D
  constructor
  · intro h
    have hidU : ∀ x y, dist (U x) (U y) ≤ dist (U x) (U y) := fun _ _ => le_rfl
    obtain ⟨F,hF,hLip⟩ := h (EuclideanSpace ℝ (Fin n)) U hidU
    exact hexact.mp ⟨F,hF,hLip⟩
  · intro hD H hH hI hC g hg
    obtain ⟨F,hF,hLip⟩ := hexact.mpr hD
    exact ose_universal_extension_of_isometry_extension (Fin n → Bool)
      (Bool × (Fin n → Bool)) (EuclideanSpace ℝ (Fin n)) U (fun x => (false,x)) D F hF hLip H g hg
