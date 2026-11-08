import AFTD.Prelude

/-!
# thermomajorization_prefix

Topic: submodular   Node: f9ed7e24ba05

Provenance: formalization of a published result. Source: arXiv:2610.35433, Eq. (190)

Given a permutation π of Fin n and a natural number k, the k-th prefix set thermomajorization_prefix π k is the finite set (Finset (Fin n)) defined as the image under π of the indices {j : Fin n | (j : ℕ) < k}.
-/

/-- The k-element prefix finset of an ordering π of energy levels {0, ..., n-1}. -/
def thermomajorization_prefix {n : ℕ} (π : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) := (Finset.univ.filter (fun j : Fin n => (j : ℕ) < k)).map π.toEmbedding
