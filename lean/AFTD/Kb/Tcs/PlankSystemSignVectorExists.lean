import AFTD.Prelude
import AFTD.Kb.Tcs.PlankEnergyDiffSingleFlip

/-!
# plank_system_sign_vector_exists

Topic: combinatorics   Node: e198ff989065

Provenance: formalization of a published result. Source: arXiv:2611.00379, Lemma 3 (A sharp plank theorem for cube annuli)

Let $V$ be a real inner product space, let $\iota$ be a finite type, let $n : \iota \to V$ be unit vectors, let $w : \iota \to \mathbb{R}$ be positive widths ($w_i > 0$ for all $i$), and let $s : \iota \to \mathbb{R}$ be shifts. Then there exists $\varepsilon : \iota \to \mathbb{R}$ such that for every $i \in \iota$, $\varepsilon_i = 1$ or $\varepsilon_i = -1$, and the vector $z = \frac{1}{2} \sum_{i \in \iota} (\varepsilon_i w_i) \cdot n_i$ satisfies $w_i / 2 \le |\langle n_i, z \rangle - s_i|$ for all $i \in \iota$.
-/

open scoped RealInnerProductSpace in
/-- Sign vector existence lemma for plank systems. -/
theorem plank_system_sign_vector_exists
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} [Fintype ι]
    (n : ι → V) (hn : ∀ i, ‖n i‖ = 1)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (s : ι → ℝ) :
    ∃ ε : ι → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      let z := (1 / 2 : ℝ) • ∑ i, (ε i * w i) • n i
      ∀ i, w i / 2 ≤ |⟪n i, z⟫ - s i| := by
  classical
  let z_of := fun (sgn : ι → ℝ) => (1 / 2 : ℝ) • ∑ j, (sgn j * w j) • n j
  let E := fun (sgn : ι → ℝ) (pt : V) => ‖pt‖ ^ 2 - ∑ j, sgn j * w j * s j
  let cost := fun (b : ι → Bool) =>
    let ε := fun j => if b j then (1 : ℝ) else -1
    E ε (z_of ε)
  have h_nonempty : (Finset.univ : Finset (ι → Bool)).Nonempty :=
    ⟨fun _ => true, Finset.mem_univ _⟩
  obtain ⟨b, -, hb⟩ := Finset.exists_max_image Finset.univ cost h_nonempty
  let ε := fun j => if b j then (1 : ℝ) else -1
  refine ⟨ε, ?_, ?_⟩
  · intro i
    dsimp [ε]
    cases b i <;> simp
  · intro z i
    let b' := Function.update b i (!b i)
    have hle : cost b' ≤ cost b := hb b' (Finset.mem_univ _)
    have h_nonneg : 0 ≤ cost b - cost b' := sub_nonneg.mpr hle
    have hε : ε i = 1 ∨ ε i = -1 := by
      dsimp [ε]
      cases b i <;> simp
    have h_upd : (fun j => if b' j then (1 : ℝ) else -1) = Function.update ε i (-ε i) := by
      ext j
      by_cases hj : j = i
      · simp [b', ε, hj]
        cases b i <;> simp
      · simp [b', ε, hj]
    have hdiff := plank_energy_diff_single_flip n hn w s ε i hε
    have heq : cost b - cost b' = 2 * w i * (ε i * (⟪n i, z_of ε⟫ - s i) - w i / 2) := by
      dsimp [cost]
      rw [h_upd]
      exact hdiff
    have h_pos : 0 < 2 * w i := by linarith [hw i]
    have h_ge : 0 ≤ ε i * (⟪n i, z_of ε⟫ - s i) - w i / 2 := by
      rw [heq] at h_nonneg
      nlinarith
    have h_le_abs : ε i * (⟪n i, z_of ε⟫ - s i) ≤ |⟪n i, z_of ε⟫ - s i| := by
      rcases hε with h1 | h2
      · simp [h1, le_abs_self]
      · rw [h2, neg_mul, one_mul]
        exact neg_le_abs (⟪n i, z_of ε⟫ - s i)
    have hz : z = z_of ε := rfl
    rw [hz]
    linarith
