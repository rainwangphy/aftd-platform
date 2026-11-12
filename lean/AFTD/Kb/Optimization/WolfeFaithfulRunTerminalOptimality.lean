import AFTD.Prelude
import AFTD.Kb.Optimization.WolfeFaithfulLinoptRun
import AFTD.Kb.Optimization.WolfeFaithfulMajorCycle

/-!
# wolfe_faithful_run_terminal_optimality

Topic: submodular   Node: 55b304fb86c5

Provenance: helper lemma. arXiv:2611.12680 Sec. 2.2

For any faithful Wolfe linopt run hrun of length k on atoms in ℝ^n with corrals S and centers w, the final center w(Fin.last k) satisfies 0 ≤ ∑ i : Fin n, w (Fin.last k) i * (q i - w (Fin.last k) i) for all atoms q ∈ atoms.
-/

/-- Terminal optimality of a faithful Wolfe linopt run: all gaps are non-negative at the end. -/
theorem wolfe_faithful_run_terminal_optimality {n : ℕ} {atoms : Set (Fin n → ℝ)} {k : ℕ}
    {S : Fin (k + 1) → Finset (Fin n → ℝ)} {w : Fin (k + 1) → (Fin n → ℝ)}
    (hrun : wolfe_faithful_linopt_run atoms k S w) :
    ∀ q ∈ atoms, 0 ≤ ∑ i : Fin n, w (Fin.last k) i * (q i - w (Fin.last k) i) := hrun.2
