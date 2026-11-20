import AFTD.Prelude

/-!
# chore_prefix_bundle

Topic: fair_division   Node: 499d6d2770b0

Provenance: formalization of a published result. Source: arXiv:2611.25892 Def. 2.1

For an allocation π : Fin m → Fin n assigning m chores (identified with their arrival rounds in Fin m) to n agents in Fin n, agent i's prefix bundle at round t : Fin m is the Finset of chores c : Fin m such that c ≤ t and π c = i.
-/

/-- Prefix bundle of agent i at round t under allocation π. -/
def chore_prefix_bundle {n m : ℕ} (π : Fin m → Fin n) (t : Fin m) (i : Fin n) : Finset (Fin m) := Finset.univ.filter (fun c => c ≤ t ∧ π c = i)
