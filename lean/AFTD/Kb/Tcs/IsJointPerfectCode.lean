import AFTD.Prelude
import AFTD.Kb.Tcs.IsJointErrorCorrectingDetecting

/-!
# is_joint_perfect_code

Topic: information   Node: aa6ab4fee35a

Provenance: formalization of a published result. Source: arXiv:2611.18156 Section IV-B

A code C ⊆ (Fin n → Fin q) is a (c, c') joint perfect code if it is a (c, c') joint error-correcting and detecting code and satisfies |C| * ∑_{i=0}^c Nat.choose n i * (q - 1)^i + ∑_{j=c+1}^{c+c'} Nat.choose n j * (q - 1)^j = q^n.
-/

/-- A code is a (c, c') joint perfect code if it is (c, c') joint error-correcting and detecting and achieves equality in the joint Hamming bound. -/
def is_joint_perfect_code {n q : ℕ} (c c' : ℕ) (C : Finset (Fin n → Fin q)) : Prop := is_joint_error_correcting_detecting c c' C ∧
    C.card * (∑ i ∈ Finset.range (c + 1), Nat.choose n i * (q - 1) ^ i) +
      ∑ j ∈ Finset.Icc (c + 1) (c + c'), Nat.choose n j * (q - 1) ^ j = q ^ n
