import AFTD.Prelude

/-!
# predecessors

Topic: general_equilibrium   Node: 09cfc83af318

Provenance: formalization of a published result. Source: arXiv:2611.16207, Section 2

Given a finite type α with decidable equality, an ordering bijection e : Fin (Fintype.card α) ≃ α mapping indices to players, and a player i : α, predecessors e i is the finite set of players e(j) for all indices j : Fin (Fintype.card α) strictly less than e.symm i.
-/

/-- The set of predecessors of player i under ordering e. -/
def predecessors {α : Type*} [DecidableEq α] [Fintype α] (e : Fin (Fintype.card α) ≃ α) (i : α) : Finset α :=
  (Finset.univ.filter (fun (j : Fin (Fintype.card α)) => j < e.symm i)).image e
