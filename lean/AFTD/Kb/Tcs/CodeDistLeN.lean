import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.CodeDist
import AFTD.Kb.Tcs.SymOrth
import AFTD.Kb.Tcs.Wt
import AFTD.Kb.Tcs.WtLeN
import AFTD.Kb.Tcs.SymBApply

/-!
# code_dist_le_n

Topic: quantum   Node: 31f9c85ce106

Provenance: helper lemma. TCSlib, `code_dist_le_n`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Code distance is at most the block length. Fix a prime $p$ and a natural number $n$, and let $V = \bbf_p^{\,n} \times \bbf_p^{\,n}$
carry the symplectic form $\omega\bigl((x,z),(x',z')\bigr) = \sum_{i} (x_i z'_i - z_i
x'_i)$. For every $\bbf_p$-subspace $S \le V$, the associated code distance $d(S)$ — the
least weight $\mathrm{wt}(v) = |\mathrm{supp}(v)|$ attained by a vector $v$ lying in the
symplectic orthogonal complement $S^{\perp_\omega}$ but not in $S$ — satisfies $d(S) \le
n$.
-/

open scoped BigOperators in
set_option linter.mathlibStandardSet false in
open scoped BigOperators in
open scoped Real in
open scoped Nat in
open Classical in
open scoped Pointwise in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
set_option relaxedAutoImplicit false in
set_option autoImplicit false in
set_option linter.unnecessarySimpa false in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
/-- `code_dist S ≤ n` since all weights are bounded by `n`. -/
lemma code_dist_le_n (S : Submodule (F p) (V n p)) :
    code_dist (n:=n) (p:=p) S ≤ n := by
  classical
  let D : Set ℕ :=
    { d | ∃ v ∈ sym_orth (n:=n) (p:=p) S, v ∉ S ∧ wt (n:=n) (p:=p) v = d }

  unfold code_dist
  change sInf D ≤ n

  by_cases hD : D = ∅
  ·
    simpa [hD] using (Nat.zero_le n)
  ·
    have hDne : D.Nonempty := Set.nonempty_iff_ne_empty.2 hD
    rcases hDne with ⟨d0, hd0mem⟩
    rcases hd0mem with ⟨v, hvS, hvnotS, hwt⟩
    have hd0 : d0 ∈ D := ⟨v, hvS, hvnotS, hwt⟩

    have hBdd : BddBelow D := ⟨0, by
      intro d hd
      exact Nat.zero_le d⟩

    have hdist_le : sInf D ≤ d0 := by
      exact csInf_le hBdd hd0

    have hd0_le : d0 ≤ n := by
      have : wt (n:=n) (p:=p) v ≤ n := wt_le_n (n:=n) (p:=p) v
      simpa [hwt] using this

    exact le_trans hdist_le hd0_le
