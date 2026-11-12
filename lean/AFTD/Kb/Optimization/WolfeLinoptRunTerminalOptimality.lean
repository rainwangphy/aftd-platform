import AFTD.Prelude
import AFTD.Kb.Optimization.WolfeLinoptRun
import AFTD.Kb.Optimization.WolfeMajorCycle

/-!
# wolfe_linopt_run_terminal_optimality

Topic: submodular   Node: 4ed701a52199

Provenance: helper lemma. arXiv:2611.12680 Lemma 1(c)

For any dimension n : ℕ, set of atoms atoms : Set (Fin n → ℝ), run length k : ℕ, corrals S : Fin (k + 1) → Finset (Fin n → ℝ), and vectors w : Fin (k + 1) → (Fin n → ℝ), if wolfe_linopt_run atoms k S w holds, then for every q ∈ atoms, 0 ≤ ∑ j : Fin n, w (Fin.last k) j * (q j - w (Fin.last k) j).
-/

/-- The terminal affine minimizer in a Wolfe linopt run satisfies global optimality over the atoms. -/
theorem wolfe_linopt_run_terminal_optimality {n : ℕ} {atoms : Set (Fin n → ℝ)} {k : ℕ}
    {S : Fin (k + 1) → Finset (Fin n → ℝ)} {w : Fin (k + 1) → (Fin n → ℝ)}
    (hrun : wolfe_linopt_run atoms k S w) :
    ∀ q ∈ atoms, 0 ≤ ∑ j : Fin n, w (Fin.last k) j * (q j - w (Fin.last k) j) := hrun.2
