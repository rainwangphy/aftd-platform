import AFTD.Prelude

/-!
# elem_symm_on

Topic: combinatorics   Node: 83dc21bb4ffc

Provenance: helper lemma. step towards parallel_uniform_merino_welsh_strict_balancing

For a finite set s of indices and a function v : ι → ℝ, elem_symm_on s k v is the sum, over all k-element subsets t of s, of the product of v over t (the k-th elementary symmetric sum of v restricted to s).
-/

/-- The k-th elementary symmetric sum of v over an arbitrary finite index set s. -/
def elem_symm_on {ι : Type*} [DecidableEq ι] (s : Finset ι) (k : ℕ) (v : ι → ℝ) : ℝ := ∑ t ∈ s.powersetCard k, ∏ i ∈ t, v i
