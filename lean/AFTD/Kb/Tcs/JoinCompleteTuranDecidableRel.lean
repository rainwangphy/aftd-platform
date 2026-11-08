import AFTD.Prelude
import AFTD.Kb.Tcs.JoinCompleteTuran

/-!
# join_complete_turan_decidableRel

Topic: graphs   Node: 58c70204367c

Provenance: formalization of a published result. Source: arXiv:2610.41371 Section 3.1

Adjacency in the join graph G_a = K_a ∨ T_{r-1}(n-a) on vertex set Fin a ⊕ Fin (n - a) is decidable.
-/

/-- Decidability of adjacency in the join graph of K_a and T_{r-1}(n-a). -/
instance join_complete_turan_decidableRel (n r a : ℕ) :
    DecidableRel (join_complete_turan n r a).Adj := by
  intro u v
  rcases u with u | u <;> rcases v with v | v <;> dsimp [join_complete_turan] <;> infer_instance
