import AFTD.Prelude

/-!
# BooleanAnalysis.sum_prod_subset_eq_prod_one_add

Topic: combinatorics   Node: 994208610d88

Provenance: helper lemma. TCSlib, `BooleanAnalysis.sum_prod_subset_eq_prod_one_add`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Sum over subsets equals a product of one plus each term. For any real numbers $c_0,\dots,c_{n-1}$, indexed by $i \in \mathrm{Fin}\,n$,
\[
\sum_{S \subseteq \{0,\dots,n-1\}} \; \prod_{i \in S} c_i \;=\; \prod_{i=0}^{n-1} (1 +
c_i),
\]
where the sum ranges over all subsets $S$ of the index set (with the empty product equal
to $1$).
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- Key identity: `∑_{S ⊆ [n]} ∏_{i∈S} c_i = ∏_i (1 + c_i)`. Used via `Finset.prod_one_add`. -/
lemma BooleanAnalysis.sum_prod_subset_eq_prod_one_add (c : Fin n → ℝ) :
    ∑ S : Finset (Fin n), ∏ i ∈ S, c i =
    ∏ i : Fin n, (1 + c i) := by
  -- Use Finset.prod_one_add: ∏_{i∈s} (1 + f i) = ∑_{t∈s.powerset} ∏_{i∈t} f i
  rw [Finset.prod_one_add Finset.univ]
  -- Now RHS = ∑ t ∈ Finset.univ.powerset, ∏ i ∈ t, c i
  -- Reindex: Finset.univ.powerset ≅ all Finset (Fin n) via id
  apply Finset.sum_nbij id
  · intro t _; exact Finset.mem_powerset.mpr (Finset.subset_univ t)
  · intro t₁ _ t₂ _ h; exact h
  · intro t ht; exact ⟨t, Finset.mem_univ t, rfl⟩
  · intro t _; rfl
