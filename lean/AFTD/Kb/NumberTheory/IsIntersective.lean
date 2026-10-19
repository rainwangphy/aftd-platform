import AFTD.Prelude

/-!
# is_intersective

Topic: elementary_number_theory   Node: 35a0f5d8a7e8

Provenance: formalization of a published result. Source: arXiv:2610.07765, Sec. 1, line 244

An integer polynomial $h \in \mathbb{Z}[X]$ is intersective if for every positive integer $m$, there exists an integer $n$ such that $h(n) \equiv 0 \pmod m$.
-/

/-- A polynomial h ∈ ℤ[X] is intersective if it has a root modulo every positive integer m. -/
def is_intersective (h : Polynomial ℤ) : Prop := ∀ m : ℕ, 0 < m → ∃ n : ℤ, h.eval n ≡ 0 [ZMOD m]
