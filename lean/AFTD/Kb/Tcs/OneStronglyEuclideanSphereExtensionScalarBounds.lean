import AFTD.Prelude

/-!
# one_strongly_euclidean_sphere_extension_scalar_bounds

Topic: algorithms   Node: 3b5ec135529f

Provenance: helper lemma. arXiv:2611.08546, Section 6.2; algebra for the symmetric extension of its two-layer cube.

For positive r and s with s squared plus twice r s equal to one, q at least one, and L equal to q divided by 2 r plus s q, the contraction factor t=sL satisfies the cross-layer identity and the inequalities needed for all positive Hamming distances.
-/

theorem one_strongly_euclidean_sphere_extension_scalar_bounds (r s q L : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hq : 1 ≤ q) (hid : s^2 + 2*r*s = 1)
    (hL : 0 ≤ L) (hdef : L * (2*r + s*q) = q) :
    let t := s*L
    q^2 * (1-t)^2 = 4*L^2*r^2 ∧ t ≤ L^2 ∧
      ∀ h : ℝ, 1 ≤ h → t^2*h ≤ L^2 * min (s^2*h^2) h := by
  dsimp only
  have hsq : s^2 ≤ 1 := by nlinarith
  have hp : 0 ≤ 2*r*s*(q-1) := by positivity
  have hmul := congrArg (fun x : ℝ => q*x) hid
  have hsL : s ≤ L := by
    have hd : 0 < 2*r+s*q := by positivity
    have hq_le : s*(2*r+s*q) ≤ q := by nlinarith
    nlinarith
  have hid2 : q*(1-s*L)=2*L*r := by nlinarith [hdef]
  have hsqeq := congrArg (fun x : ℝ => x^2) hid2
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hsqeq]
  · nlinarith [mul_nonneg hL (sub_nonneg.mpr hsL)]
  · intro h hh
    rw [mul_min_of_nonneg _ _ (sq_nonneg L)]
    apply le_min
    · have hhh : 0 ≤ h^2-h := by nlinarith
      have := mul_nonneg (sq_nonneg (s*L)) hhh
      nlinarith
    · have hp2 : 0 ≤ L^2*h*(1-s^2) := by positivity
      nlinarith
