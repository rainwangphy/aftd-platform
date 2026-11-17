import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.Op869BoundedAdversaryForcesUnbounded
import AFTD.Kb.Tcs.Op869AdversaryForcesSound
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.ColorsUsed
import AFTD.Kb.Tcs.Op869AdversaryForces
import AFTD.Kb.Tcs.IsOnlineColoringAlg
import AFTD.Kb.Tcs.ProperlyColorsKColorable

/-!
# op869_bounded_adversary_forces_sound

Topic: online_algorithms   Node: 016d2fef9be5

Provenance: helper lemma. step towards op869_online_coloring_deterministic_lower_bound

A winning 1-fold bounded adversary position started from the empty position yields a k-colourable graph on which every causal proper algorithm uses at least K colours.
-/

/-- Bridge from the bounded game to the target's graph language: a win from the empty position beats every causal proper algorithm. -/
theorem op869_bounded_adversary_forces_sound {n : ℕ} (k K D : ℕ)
    (A : SimpleGraph (Fin n) → Fin n → ℕ)
    (hA : IsOnlineColoringAlg A) (hproper : ProperlyColorsKColorable k A)
    (h : op869_bounded_adversary_forces k 1 K D n 0 (fun _ : Fin n => ∅) (fun _ : Fin n => ∅)) :
    ∃ G : SimpleGraph (Fin n), G.Colorable k ∧ K ≤ colorsUsed (A G) := by
  have hplay := op869_bounded_adversary_forces_unbounded k 1 K D n 0
    (fun _ : Fin n => ∅) (fun _ : Fin n => ∅) h
  exact op869_adversary_forces_sound k K A hA hproper n 0
    (fun _ : Fin n => ∅) (fun _ : Fin n => ∅) hplay (by intro a ha; omega)
