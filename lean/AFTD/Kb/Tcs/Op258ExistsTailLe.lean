import AFTD.Prelude
import AFTD.Kb.Tcs.Op258Bounded

/-!
# op_258_exists_tail_le

Topic: combinatorics   Node: d3004c3d482f

Provenance: helper lemma. step towards op_258_forces_step

For any positive profile with finite ENNReal sum and any ε > 0, there is a cutoff C such that any finite set of colours strictly above C has sum less than ε.
-/

/-- For any positive profile with finite ENNReal sum and any ε > 0, there is a cutoff C such that any finite set of colours strictly above C has sum less than ε. -/
theorem op_258_exists_tail_le (a : ℕ+ → ℝ) (hpos : ∀ i, 0 < a i)
    (hsum_fin : (∑' i : ℕ+, ENNReal.ofReal (a i)) ≠ ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℕ, ∀ I : Finset ℕ+, (∀ i ∈ I, C < (i : ℕ)) → (∑ i ∈ I, a i) < ε := by
  have h_summable : Summable a := by
    have h_summable_nn : Summable (fun i => (a i).toNNReal) := by
      rwa [← ENNReal.tsum_coe_ne_top_iff_summable]
    have h_summable_real : Summable (fun i => ((a i).toNNReal : ℝ)) :=
      NNReal.summable_coe.2 h_summable_nn
    have heq : (fun i => ((a i).toNNReal : ℝ)) = a := by
      ext i
      exact Real.coe_toNNReal _ (le_of_lt (hpos i))
    rwa [heq] at h_summable_real
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp h_summable ε hε
  use s.sup (fun j => (j : ℕ))
  intro I hI
  have hdisj : Disjoint I s := by
    rw [Finset.disjoint_left]
    intro i hi hs_in
    have h1 := Finset.le_sup (s := s) (f := fun j => (j : ℕ)) hs_in
    have h2 := hI i hi
    omega
  specialize hs I hdisj
  have hnonneg : 0 ≤ ∑ i ∈ I, a i := Finset.sum_nonneg fun i _ => le_of_lt (hpos i)
  rwa [Real.norm_of_nonneg hnonneg] at hs
