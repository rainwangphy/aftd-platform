import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CanForce
import AFTD.Kb.GameTheoryEconomics.HasTypeWManipulation
import AFTD.Kb.GameTheoryEconomics.VotingOptionSet

/-!
# has_type_w_manipulation_of_can_force

Topic: social_choice   Node: 623a967e193b

Provenance: helper lemma. arXiv:2611.26224

If an alternative v is in the option set of coalition C at profile P under voting rule f, C can force alternative x, and every member of C strictly prefers x to v under P, then there exists a reported profile P_dev such that C has an obvious group manipulation of type (W) at P by reporting P_dev.
-/

/-- A coalition has a type (W) manipulation if it can force an alternative preferred by all its members to an outcome in its truthful option set. -/
lemma has_type_w_manipulation_of_can_force {N A : Type*} (f : (N → LinearOrder A) → A)
    (C : Finset N) (P : N → LinearOrder A) (x v : A)
    (hv : v ∈ voting_option_set f C P)
    (hforce : can_force f C x)
    (hpref : ∀ i ∈ C, @LT.lt A (P i).toLT v x) :
    ∃ P_dev, has_type_w_manipulation f C P P_dev := by
  obtain ⟨P_dev, hF⟩ := hforce
  exact ⟨P_dev, v, hv, fun y hy i hi => by
    rw [hF, Set.mem_singleton_iff] at hy
    subst hy
    exact hpref i hi⟩
