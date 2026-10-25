import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryQuarticRelationsDecomposable

/-!
# binary_quartic_relations_rank_le_two

Topic: quantum   Node: 89e4192e2f55

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

A finite binary matrix satisfying all the four-index alternating relations has rank at most two.
-/

theorem binary_quartic_relations_rank_le_two {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (hQ : ∀ i j k l, Q i j * Q k l + Q i k * Q j l + Q i l * Q j k = 0) :
    Q.rank ≤ 2 := by
  obtain ⟨a, b, hab⟩ := binary_quartic_relations_decomposable Q hQ
  have he : Q = Matrix.vecMulVec a b + Matrix.vecMulVec b a := by
    ext i j
    exact hab i j
  let A : Matrix (Fin n) (Fin 2) (ZMod 2) := fun i => ![a i, b i]
  let B : Matrix (Fin 2) (Fin n) (ZMod 2) := ![b, a]
  have hf : Q = A * B := by
    rw [he]
    ext i j
    change a i * b j + b i * a j = ∑ k : Fin 2, A i k * B k j
    simp [A, B, Fin.sum_univ_two]
  calc
    Q.rank = (A * B).rank := by rw [hf]
    _ ≤ A.rank := Matrix.rank_mul_le_left _ _
    _ ≤ 2 := Matrix.rank_le_width A
