import AFTD.Prelude

/-!
# is_two_regular

Topic: elementary_number_theory   Node: a96a9277a50f

Provenance: formalization of a published result. Source: arXiv:2611.01243 Sec. 6; Allouche and Shallit, TCS 1992

An integer sequence $f : \mathbb{N} \to \mathbb{Z}$ is 2-regular if the $\mathbb{Z}$-submodule of $\mathbb{Z}^\mathbb{N}$ spanned by its 2-kernel $\{n \mapsto f(2^e n + r) : e \ge 0, 0 \le r < 2^e\}$ is finitely generated.
-/

/-- A sequence f : ℕ → ℤ is 2-regular if the ℤ-submodule spanned by its 2-kernel is finitely generated. -/
def is_two_regular (f : ℕ → ℤ) : Prop := (Submodule.span ℤ { g : ℕ → ℤ | ∃ (e r : ℕ), r < 2 ^ e ∧ g = fun n => f (2 ^ e * n + r) }).FG
