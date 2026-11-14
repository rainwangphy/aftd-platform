import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterSequenceLatticeS4Summable
import AFTD.Kb.Physics.EnergyFilterSequenceConvolutionPointwiseSummable
import AFTD.Kb.Physics.EnergyFilterFiniteCubeProductCs
import AFTD.Kb.Physics.EnergyFilterAbsConvolutionControl

/-!
# energy_filter_sequence_abs_quartic_cycle_summable

Topic: statistical_mechanics   Node: 38bdb55ca530

Provenance: helper lemma. OP-892: alternative reduction via centered binomial correlations; experiment 26245.

For every real ℓ^(4/3) sequence a, the absolute values of a(u)a(v)a(w)a(u−v+w) are summable over integer triples (u,v,w).
-/

theorem energy_filter_sequence_abs_quartic_cycle_summable (a : ℤ → ℝ) (ha : Memℓp a (4 / 3)) :
    Summable (fun p : ℤ × ℤ × ℤ =>
      |a p.1 * a p.2.1 * a p.2.2 * a (p.1 - p.2.1 + p.2.2)|) := by
  obtain ⟨hconv,hconv2⟩ := energy_filter_abs_convolution_control a ha
  let G : ℤ × ℤ × ℤ → ℝ := fun p =>
    |a p.2.1 * a (p.1-p.2.1)| * |a p.2.2 * a (p.1-p.2.2)|
  have hprod (m : ℤ) : Summable (fun p : ℤ × ℤ =>
      |a p.1 * a (m-p.1)| * |a p.2 * a (m-p.2)|) := by
    have hnorm : Summable (fun j : ℤ => ‖|a j * a (m-j)|‖) := by
      simpa [Real.norm_eq_abs] using hconv m
    exact summable_mul_of_summable_norm
      (f := fun j : ℤ => |a j * a (m-j)|) (g := fun j : ℤ => |a j * a (m-j)|) hnorm hnorm
  have hsum (m : ℤ) : (∑' p : ℤ × ℤ,
      |a p.1 * a (m-p.1)| * |a p.2 * a (m-p.2)|) =
      (∑' j : ℤ, |a j * a (m-j)|)^2 := by
    have hnorm : Summable (fun j : ℤ => ‖|a j * a (m-j)|‖) := by
      simpa [Real.norm_eq_abs] using hconv m
    have hh := tsum_mul_tsum_of_summable_norm hnorm hnorm
    simpa [pow_two] using hh.symm
  have houter : Summable (fun m : ℤ => ∑' p : ℤ × ℤ,
      |a p.1 * a (m-p.1)| * |a p.2 * a (m-p.2)|) := by
    convert hconv2 using 1
    funext m
    exact hsum m
  have hG : Summable G := by
    apply (summable_prod_of_nonneg (show 0 ≤ G from fun p => mul_nonneg (abs_nonneg _) (abs_nonneg _))).2
    constructor
    · intro m
      exact hprod m
    · exact houter
  let e : (ℤ × ℤ × ℤ) ≃ (ℤ × ℤ × ℤ) := {
    toFun := fun p => (p.1+p.2.2, p.1, p.2.1)
    invFun := fun p => (p.2.1, p.2.2, p.1-p.2.1)
    left_inv := by intro p; rcases p with ⟨u,v,w⟩; simp
    right_inv := by intro p; rcases p with ⟨m,u,v⟩; simp }
  have heq : ∀ p : ℤ × ℤ × ℤ,
      G (e p) = |a p.1 * a p.2.1 * a p.2.2 * a (p.1-p.2.1+p.2.2)| := by
    intro p
    rcases p with ⟨u,v,w⟩
    dsimp [G,e]
    have h1 : u+w-u = w := by omega
    have h2 : u+w-v = u-v+w := by omega
    rw [h1,h2]
    simp only [abs_mul]
    ring
  have hQ := (e.summable_iff).2 hG
  convert hQ using 1
  funext p
  exact (heq p).symm
