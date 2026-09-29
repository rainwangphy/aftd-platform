import AFTD.Prelude
import AFTD.Kb.Tcs.TimeBounded
import AFTD.Kb.Tcs.PolyTimeBounded
import AFTD.Kb.Tcs.ExpTimeBounded
import AFTD.Kb.Tcs.TimeBoundedMono

/-!
# poly_time_subset_exp_time

Topic: complexity_basics   Node: f079c992dbcf

Every language in P is in EXP: if L is decidable in time p(n) for a polynomial p, then L is decidable in time 2^(p(n)).
-/

/-- P is contained in EXP. -/
theorem poly_time_subset_exp_time {Γ : Type} {L : Language Γ} (h : PolyTimeBounded Γ L) :
    ExpTimeBounded Γ L := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, time_bounded_mono (fun n => (p.eval n).lt_two_pow_self.le) hp⟩
