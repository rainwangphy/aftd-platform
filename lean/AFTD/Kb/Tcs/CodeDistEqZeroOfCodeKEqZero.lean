import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.IsIsotropic
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.CodeDist
import AFTD.Kb.Tcs.CodeK
import AFTD.Kb.Tcs.FinrankLeNOfIsotropic
import AFTD.Kb.Tcs.FinrankSymOrth
import AFTD.Kb.Tcs.SymOrth
import AFTD.Kb.Tcs.Wt
import AFTD.Kb.Tcs.SymBApply

/-!
# code_dist_eq_zero_of_code_k_eq_zero

Topic: quantum   Node: 76ba7d2be18d

Provenance: helper lemma. TCSlib, `code_dist_eq_zero_of_code_k_eq_zero`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Zero logical dimension forces zero distance. Let $p$ be a prime and let $S$ be a subspace of the symplectic space $V = \bbf_p^n
\times \bbf_p^n$. If $S$ is isotropic and its logical dimension vanishes, $k(S) = 0$,
then the code distance vanishes as well, $d(S) = 0$.
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
lemma code_dist_eq_zero_of_code_k_eq_zero
    (S : Submodule (F p) (V n p))
    (hS : IsIsotropic (n:=n) (p:=p) S)
    (hk : code_k (n:=n) (p:=p) S = 0) :
    code_dist (n:=n) (p:=p) S = 0 := by
  classical
  have hfin_le_n : Module.finrank (F p) S ≤ n :=
    finrank_le_n_of_isotropic (n:=n) (p:=p) S hS
  have hk' : n - Module.finrank (F p) S = 0 := by
    simpa [code_k] using hk
  have hn_le_fin : n ≤ Module.finrank (F p) S :=
    (Nat.sub_eq_zero_iff_le).1 hk'
  have hfin_eq : Module.finrank (F p) S = n :=
    Nat.le_antisymm hfin_le_n hn_le_fin

  have hfin_orth :
      Module.finrank (F p) (sym_orth (n:=n) (p:=p) S)
        = Module.finrank (F p) S := by
    calc
      Module.finrank (F p) (sym_orth (n:=n) (p:=p) S)
          = 2 * n - Module.finrank (F p) S := by
            simpa using finrank_sym_orth (n:=n) (p:=p) S
      _ = 2 * n - n := by simp [hfin_eq]
      _ = n := by
            simpa [two_mul] using (Nat.add_sub_cancel_left n n)
      _ = Module.finrank (F p) S := by simp [hfin_eq]

  have hEq : S = sym_orth (n:=n) (p:=p) S := by
    apply Submodule.eq_of_le_of_finrank_eq hS
    simpa using hfin_orth.symm

  unfold code_dist
  rw [← hEq]

  have hEmpty :
      {d : ℕ | ∃ v ∈ S, v ∉ S ∧ wt (n:=n) (p:=p) v = d} = (∅ : Set ℕ) := by
    ext d
    constructor
    · rintro ⟨v, hvS, hvnotS, -⟩
      exact (hvnotS hvS).elim
    · intro hd
      cases hd

  rw [hEmpty]
  simp
