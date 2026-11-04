import AFTD.Prelude
import AFTD.Kb.Tcs.NormSubSmulSq
import AFTD.Kb.Tcs.PlankSignedSumFlip

/-!
# plank_energy_diff_single_flip

Topic: combinatorics   Node: 14ac6254fec8

Provenance: helper lemma. arXiv:2611.00379, Lemma 3 proof

Let $V$ be a real inner product space and $\iota$ a finite type with decidable equality. Let $n : \iota \to V$ be unit vectors, $w : \iota \to \mathbb{R}$ widths, $s : \iota \to \mathbb{R}$ shifts, $\varepsilon : \iota \to \mathbb{R}$ signs, and $i \in \iota$ with $\varepsilon_i = 1$ or $\varepsilon_i = -1$. Let $\varepsilon'$ be $\varepsilon$ with the sign at $i$ flipped, let $z = \frac{1}{2}\sum_j (\varepsilon_j w_j) \cdot n_j$ and $z' = \frac{1}{2}\sum_j (\varepsilon'_j w_j) \cdot n_j$. Define the energy $E(\sigma, v) = \|v\|^2 - \sum_j \sigma_j w_j s_j$. Then $E(\varepsilon, z) - E(\varepsilon', z') = 2 w_i (\varepsilon_i (\langle n_i, z \rangle - s_i) - w_i / 2)$.
-/

open scoped RealInnerProductSpace in
/-- Energy difference under flipping a single sign in a plank system. -/
lemma plank_energy_diff_single_flip
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ι → V) (hn : ∀ i, ‖n i‖ = 1)
    (w : ι → ℝ) (s : ι → ℝ) (ε : ι → ℝ) (i : ι) (hε : ε i = 1 ∨ ε i = -1) :
    let ε' := Function.update ε i (-ε i)
    let z := (1 / 2 : ℝ) • ∑ j, (ε j * w j) • n j
    let z' := (1 / 2 : ℝ) • ∑ j, (ε' j * w j) • n j
    let E := fun (sgn : ι → ℝ) (pt : V) => ‖pt‖ ^ 2 - ∑ j, sgn j * w j * s j
    E ε z - E ε' z' = 2 * w i * (ε i * (⟪n i, z⟫ - s i) - w i / 2) := by
  dsimp only
  have hsum : (∑ j, Function.update ε i (-ε i) j * w j * s j)
      = (∑ j, ε j * w j * s j) - 2 * (ε i * w i * s i) := by
    have key : (∑ j, Function.update ε i (-ε i) j * w j * s j) - (∑ j, ε j * w j * s j)
        = - 2 * (ε i * w i * s i) := by
      rw [← Finset.sum_sub_distrib]
      have hzero : ∀ b ∈ Finset.univ, b ≠ i →
          (Function.update ε i (-ε i) b * w b * s b - ε b * w b * s b) = 0 := by
        intro b hb hne
        simp only [Function.update, dif_neg hne, sub_self]
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) hzero]
      simp [Function.update]
      ring
    linarith
  have heps : ε i ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hsq : (ε i * w i) ^ 2 = w i ^ 2 := by
    have : (ε i * w i) ^ 2 = ε i ^ 2 * w i ^ 2 := by ring
    rw [this, heps]; ring
  rw [plank_signed_sum_flip n w ε i]
  rw [norm_sub_smul_sq _ (n i) (hn i) (ε i * w i)]
  rw [hsum]
  nlinarith [hsq]
