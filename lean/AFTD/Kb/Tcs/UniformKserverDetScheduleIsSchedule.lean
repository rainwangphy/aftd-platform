import AFTD.Prelude
import AFTD.Kb.Tcs.UniformKserverDetAlgServes
import AFTD.Kb.Tcs.UniformKserverDetSchedule
import AFTD.Kb.Tcs.UniformKserverIsSchedule

/-!
# uniform_kserver_det_schedule_is_schedule

Topic: online_algorithms   Node: 1bbe8d378431

Provenance: helper lemma. arXiv:2610.37192 Sec. 6

For a natural number k, a family of types M indexed by Fin k, an algorithm A : List (∀ i, M i) → (∀ i, M i) satisfying uniform_kserver_det_alg_serves A, and any request sequence ρ : List (∀ i, M i), the schedule uniform_kserver_det_schedule A ρ is a valid schedule for ρ, satisfying uniform_kserver_is_schedule ρ (uniform_kserver_det_schedule A ρ).
-/

/-- A valid deterministic online algorithm produces a valid schedule on any request sequence. -/
theorem uniform_kserver_det_schedule_is_schedule {k : ℕ} {M : Fin k → Type*}
    (A : List (∀ i, M i) → (∀ i, M i)) (hA : uniform_kserver_det_alg_serves A)
    (ρ : List (∀ i, M i)) :
    uniform_kserver_is_schedule ρ (uniform_kserver_det_schedule A ρ) := by
  dsimp [uniform_kserver_is_schedule, uniform_kserver_det_schedule]
  refine ⟨by simp, ?_⟩
  intro pair hpair
  rw [List.mem_iff_getElem] at hpair
  rcases hpair with ⟨t, ht, rfl⟩
  rw [List.getElem_zip]
  dsimp
  have ht_len : t < ρ.length := by
    have := ht
    rw [List.length_zip] at this
    exact lt_of_lt_of_le this (min_le_right _ _)
  simp only [List.getElem_map, List.getElem_range]
  rw [List.take_add_one, List.getElem?_eq_getElem ht_len]
  exact hA (ρ.take t) ρ[t]
