import AFTD.Prelude
import AFTD.Kb.Tcs.CanonicalPermutationNegativeDependencyCardBound
import AFTD.Kb.Tcs.FiniteLopsidedAvoidanceOfCardBound

/-!
# canonical_permutation_avoidance_of_local_lemma

Topic: graphs   Node: f8da8ebfe8f7

Provenance: formalization of a published result. Source: Using Lovász Local Lemma in the Space of Random Injections, Electronic Journal of Combinatorics 14 (2007), R63, DOI 10.37236/981, Theorem 1 and Lemma 3. Specialization to permutations of Fin n and the domain/range-intersection supergraph of the canonical conflict graph; this is a statement only, not an imported proof.

For finitely many injective partial assignments on n points, if weights in [0,1) satisfy the asymmetric local-lemma inequalities for the graph connecting assignments with overlapping domains or ranges, some permutation avoids every assignment.
-/

theorem canonical_permutation_avoidance_of_local_lemma
    {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ) (hn : 0 < n)
    (D : I → Finset (Fin n)) (f : I → Fin n → Fin n)
    (hD : ∀ i, (D i).Nonempty)
    (hf : ∀ i, Set.InjOn (f i) (↑(D i) : Set (Fin n)))
    (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hprob : ∀ i, (1 : ℝ) / (n.descFactorial (D i).card : ℝ) ≤
      x i * ∏ j ∈ Finset.univ.filter (fun j => j ≠ i ∧
        (¬ Disjoint (D i) (D j) ∨
          ¬ Disjoint ((D i).image (f i)) ((D j).image (f j)))), (1 - x j)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, ∃ v ∈ D i, σ v ≠ f i v := by
  classical
  let A : I → Finset (Equiv.Perm (Fin n)) := fun i =>
    Finset.univ.filter (fun σ => ∀ v ∈ D i, σ v = f i v)
  let N : I → Finset I := fun i => Finset.univ.filter (fun j => j ≠ i ∧
    (¬ Disjoint (D i) (D j) ∨
      ¬ Disjoint ((D i).image (f i)) ((D j).image (f j))))
  have hmem : ∀ σ i, σ ∉ A i ↔ ∃ v ∈ D i, σ v ≠ f i v := by
    intro σ i
    simp [A, not_forall]
  have hdep : ∀ i (S : Finset I), i ∉ S → Disjoint S (N i) →
      ((A i ∩ Finset.univ.filter (fun σ => ∀ j ∈ S, σ ∉ A j)).card : ℝ) ≤
        (1 : ℝ) / (n.descFactorial (D i).card : ℝ) *
          ((Finset.univ.filter (fun σ => ∀ j ∈ S, σ ∉ A j)).card : ℝ) := by
    intro i S hi hd
    have hnon : ∀ j ∈ S, Disjoint (D i) (D j) ∧
        Disjoint ((D i).image (f i)) ((D j).image (f j)) := by
      intro j hj
      have hjN : j ∉ N i := fun h => Finset.disjoint_left.mp hd hj h
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      have hh : ¬ (¬ Disjoint (D i) (D j) ∨
          ¬ Disjoint ((D i).image (f i)) ((D j).image (f j))) := by
        intro h
        exact hjN (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji, h⟩)
      tauto
    have hc := canonical_permutation_negative_dependency_card_bound
      (D i) (f i) (hf i) S D f (fun j hj => (hnon j hj).1) (fun j hj => (hnon j hj).2)
    have hc0 : n.descFactorial (D i).card *
        (A i ∩ Finset.univ.filter (fun σ => ∀ j ∈ S, σ ∉ A j)).card ≤
          (Finset.univ.filter (fun σ => ∀ j ∈ S, σ ∉ A j)).card := by
      convert hc using 1
      · congr 1
        · simp
        · congr 1
          ext σ
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_inter, not_forall, _root_.not_imp, exists_prop]
          tauto
      · congr 1
        ext σ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem]
    have hdpos : 0 < (n.descFactorial (D i).card : ℝ) := by
      exact_mod_cast Nat.descFactorial_pos.mpr
        (show (D i).card ≤ n by simpa using Finset.card_le_univ (D i))
    have hc' : (n.descFactorial (D i).card : ℝ) *
        ((A i ∩ Finset.univ.filter (fun σ => ∀ j ∈ S, σ ∉ A j)).card : ℝ) ≤
          ((Finset.univ.filter (fun σ => ∀ j ∈ S, σ ∉ A j)).card : ℝ) := by
      exact_mod_cast hc0
    have hdiv : ((A i ∩ Finset.univ.filter (fun σ => ∀ j ∈ S, σ ∉ A j)).card : ℝ) ≤
        ((Finset.univ.filter (fun σ => ∀ j ∈ S, σ ∉ A j)).card : ℝ) /
          (n.descFactorial (D i).card : ℝ) :=
      (le_div_iff₀ hdpos).mpr (by simpa [mul_comm] using hc')
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hdiv
  obtain ⟨σ, hσ⟩ := finite_lopsided_avoidance_of_card_bound A N
    (fun i => (1 : ℝ) / (n.descFactorial (D i).card : ℝ)) x hx0 hx1 hdep hprob
  exact ⟨σ, fun i => (hmem σ i).mp (hσ i)⟩
