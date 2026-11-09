import AFTD.Prelude

/-!
# permExtendLast

Topic: combinatorics   Node: 28c8578203bb

Provenance: formalization of a published result. Source: arXiv:2611.05397 Definition 6

The canonical extension of a permutation of Fin n to a permutation of Fin (n + 1) that fixes the trailing element Fin.last n.
-/

/-- Extend a permutation of Fin n to Fin (n + 1) fixing the last element. -/
def permExtendLast {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) := (finSuccEquiv' (Fin.last n)).trans ((Equiv.optionCongr e).trans (finSuccEquiv' (Fin.last n)).symm)
