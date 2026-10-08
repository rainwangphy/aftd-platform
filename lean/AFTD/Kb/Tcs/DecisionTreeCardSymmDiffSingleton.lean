import AFTD.Prelude

/-!
# DecisionTree.card_symmDiff_singleton

Topic: circuits   Node: 2efc4632006c

Provenance: helper lemma. TCSlib, `DecisionTree.card_symmDiff_singleton`. Lean proof by Hydroxyi, Owen McGinty, Seyoon Ragavan (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean (Apache-2.0); 1 verbatim; compiled here.

Cardinality under singleton symmetric difference. Let $S$ be a finite subset of $\{0,1,\dots,n-1\}$ and let $i$ be one of these indices.
Then the symmetric difference $S \triangle \{i\}$ satisfies
\[
\abs{S} - 1 \le \abs{S \triangle \{i\}},
\]
where $\abs{S} - 1$ denotes truncated subtraction on the natural numbers (so it is $0$
when $S$ is empty).
-/

variable {n : ℕ} in
lemma DecisionTree.card_symmDiff_singleton (S : Finset (Fin n)) (i : Fin n) :
    S.card - 1 ≤ (symmDiff S {i}).card := by
  by_cases h : i ∈ S
  · have he : symmDiff S {i} = S.erase i := by
      ext j
      by_cases hj : j = i <;>
        simp [Finset.mem_symmDiff, Finset.mem_erase, hj, h]
    rw [he, Finset.card_erase_of_mem h]
  · have he : symmDiff S {i} = insert i S := by
      ext j
      by_cases hj : j = i <;>
        simp [Finset.mem_symmDiff, Finset.mem_insert, hj, h]
    rw [he, Finset.card_insert_of_notMem h]
    omega
