import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryDeletionCollision

/-!
# min_binary_deletion_collision

Topic: information   Node: 053ef9ca4030

Provenance: formalization of a published result. Source: arXiv:2611.01064: Maximal input entropy for binary two-deletion and two-insertion channels

For natural numbers k and n, min_binary_deletion_collision k n is the minimum over all binary words w of length n of binary_deletion_collision k n w.
-/

/-- The minimum k-deletion collision sum over all binary words of length n. -/
def min_binary_deletion_collision (k n : ℕ) : ℕ := (Finset.univ.image (fun w : Fin n → Bool => binary_deletion_collision k n w)).min'
    (Finset.Nonempty.image Finset.univ_nonempty _)
