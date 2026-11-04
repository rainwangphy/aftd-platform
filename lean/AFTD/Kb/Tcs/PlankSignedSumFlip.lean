import AFTD.Prelude

/-!
# plank_signed_sum_flip

Topic: combinatorics   Node: 16a022730c0b

Provenance: helper lemma. arXiv:2611.00379, Lemma 3 proof

Let $V$ be a real vector space and $\iota$ a finite type with decidable equality. Given vectors $n : \iota \to V$, weights $w : \iota \to \mathbb{R}$, signs $\varepsilon : \iota \to \mathbb{R}$, and an index $i \in \iota$, replacing $\varepsilon_i$ with $-\varepsilon_i$ changes $\frac{1}{2} \sum_{j \in \iota} (\varepsilon_j w_j) \cdot n_j$ to $\frac{1}{2} \sum_{j \in \iota} (\varepsilon_j w_j) \cdot n_j - (\varepsilon_i w_i) \cdot n_i$.
-/

/-- Effect on a signed sum of vectors when flipping a single coordinate sign. -/
lemma plank_signed_sum_flip
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ι → V) (w : ι → ℝ) (ε : ι → ℝ) (i : ι) :
    (1 / 2 : ℝ) • ∑ j, (Function.update ε i (-ε i) j * w j) • n j =
      (1 / 2 : ℝ) • ∑ j, (ε j * w j) • n j - (ε i * w i) • n i := by
  have h : ∑ j, (Function.update ε i (-ε i) j * w j) • n j
      = (∑ j, (ε j * w j) • n j) - (2 : ℝ) • ((ε i * w i) • n i) := by
    rw [← Finset.sum_erase_add _ (fun j => (Function.update ε i (-ε i) j * w j) • n j)
      (Finset.mem_univ i)]
    rw [← Finset.sum_erase_add _ (fun j => (ε j * w j) • n j) (Finset.mem_univ i)]
    simp only [Function.update_apply, Finset.mem_univ, and_true, ne_eq, if_true]
    have hcongr : (∑ x ∈ Finset.univ.erase i, ((if x = i then -ε i else ε x) * w x) • n x)
        = ∑ x ∈ Finset.univ.erase i, (ε x * w x) • n x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_erase] at hx
      rw [if_neg hx.1]
    rw [hcongr]
    module
  rw [h, smul_sub, smul_smul]
  norm_num
