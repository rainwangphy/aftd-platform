import AFTD.Prelude
import AFTD.Kb.Tcs.IsJointlyMeasurableOn

/-!
# certifies_noiseless_codes

Topic: quantum   Node: 4b1251c7fc95

Provenance: formalization of a published result. Source: arXiv:2610.37347 Discussion and outlook, paragraph 3

Given $M : \mathbb{R} \to \mathrm{Fin}\,k \to \mathrm{Matrix}(\mathrm{Fin}\,d)(\mathrm{Fin}\,d)\mathbb{C}$ and $s_{\max} : \mathbb{R}$, the predicate asserts that: $1 < s_{\max}$; for all $s \in [0, s_{\max}]$ and all $j \in \mathrm{Fin}\,k$, $M(s, j)$ and $1 - M(s, j)$ are positive semidefinite; for all $s \in [0, s_{\max}]$, the family $M(s)$ is jointly measurable on $1$ via is_jointly_measurable_on if and only if $s \le 1$; and for every natural number $D$ with $d \le D$, natural number $m$, and Kraus operators $K : \mathrm{Fin}\,m \to \mathrm{Matrix}(\mathrm{Fin}\,d)(\mathrm{Fin}\,D)\mathbb{C}$ satisfying the trace-preserving condition $\sum_i K_i^\dagger K_i = 1$, letting $N(X) = \sum_i K_i X K_i^\dagger$ and $\Lambda(Y) = \sum_i K_i^\dagger Y K_i$, there exists an isometry $W \in \mathrm{Matrix}(\mathrm{Fin}\,D)(\mathrm{Fin}\,d)\mathbb{C}$ with $W^\dagger W = 1$ such that $N(W \rho W^\dagger) = \rho$ for all density matrices $\rho$ (positive semidefinite with trace 1) if and only if for all $s \in [0, s_{\max}]$, the image family under $\Lambda$ is jointly measurable on $1$ via is_jointly_measurable_on if and only if $s \le 1$.
-/

/-- A parametrized family of k binary measurements on C^d with parameter bound s_max > 1 certifies noiseless quantum codes if its compatibility threshold is 1 and preservation of this threshold under any trace-preserving completely positive map N with Kraus operators K is equivalent to the existence of a noiseless code isometry W. -/
def certifies_noiseless_codes {d k : ℕ}
    (M : ℝ → Fin k → Matrix (Fin d) (Fin d) ℂ) (s_max : ℝ) : Prop := open scoped ComplexOrder Matrix in
  1 < s_max ∧
  (∀ s ∈ Set.Icc 0 s_max, ∀ j : Fin k, (M s j).PosSemidef ∧ (1 - M s j).PosSemidef) ∧
  (∀ s ∈ Set.Icc 0 s_max, is_jointly_measurable_on (M s) 1 ↔ s ≤ 1) ∧
  ∀ (D : ℕ) (_ : d ≤ D) (m : ℕ) (K : Fin m → Matrix (Fin d) (Fin D) ℂ)
    (_hK : ∑ i, (K i)ᴴ * K i = 1),
    let N : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin d) (Fin d) ℂ :=
      fun X => ∑ i, K i * X * (K i)ᴴ
    let Λ : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin D) (Fin D) ℂ :=
      fun Y => ∑ i, (K i)ᴴ * Y * K i
    (∃ W : Matrix (Fin D) (Fin d) ℂ, Wᴴ * W = 1 ∧
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 → N (W * ρ * Wᴴ) = ρ) ↔
    (∀ s ∈ Set.Icc 0 s_max, is_jointly_measurable_on (fun j => Λ (M s j)) 1 ↔ s ≤ 1)
