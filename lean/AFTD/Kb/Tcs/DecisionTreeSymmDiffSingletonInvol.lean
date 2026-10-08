import AFTD.Prelude

/-!
# DecisionTree.symmDiff_singleton_invol

Topic: circuits   Node: 2c138c3e4550

Provenance: helper lemma. TCSlib, `DecisionTree.symmDiff_singleton_invol`. Lean proof by Hydroxyi, Owen McGinty, Seyoon Ragavan (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean (Apache-2.0); 1 verbatim; compiled here.

Symmetric difference with a singleton is an involution. Fix $n \in \bbn$ and an index $i \in \{0, 1, \dots, n-1\}$. The map on subsets of $\{0,
1, \dots, n-1\}$ that sends each set $S$ to its symmetric difference $S \triangle \{i\}$
with the singleton $\{i\}$ is an involution: applying it twice returns every set to
itself, so $\bigl(S \triangle \{i\}\bigr) \triangle \{i\} = S$ for all $S$.
-/

variable {n : ℕ} in
lemma DecisionTree.symmDiff_singleton_invol (i : Fin n) :
    Function.Involutive (fun S : Finset (Fin n) => symmDiff S {i}) := fun S => by
  simp only [symmDiff_assoc, symmDiff_self, symmDiff_bot]
