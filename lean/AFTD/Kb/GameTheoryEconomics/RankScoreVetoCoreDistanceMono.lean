import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsConsistentPseudometric
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# rank_score_veto_core_distance_mono

Topic: social_choice   Node: cda2038e5a86

Provenance: helper lemma. step towards rank_score_veto_core_tightness_conjecture

In a pseudometric space on V ⊕ C consistent with prof, if candidate x is weakly better than y for voter v then v is weakly closer to y than to x ('better is closer').
-/

/-- Consistency of the pseudometric with the profile, as a monotone-distance statement. -/
theorem rank_score_veto_core_distance_mono :
    ∀ (C V : Type*) [Fintype C] [Fintype V] [PseudoMetricSpace (V ⊕ C)]
      (prof : V → LinearOrder C),
      is_consistent_pseudometric V C prof →
      ∀ (v : V) (x y : C), (prof v).le x y →
        dist (Sum.inl v : V ⊕ C) (Sum.inr y) ≤ dist (Sum.inl v : V ⊕ C) (Sum.inr x) := by
  intro C V _ _ _ prof h v x y hxy
  let _ : LinearOrder C := prof v
  by_contra hcon
  exact absurd (h v x y (not_le.mp hcon)) (not_lt_of_ge hxy)
