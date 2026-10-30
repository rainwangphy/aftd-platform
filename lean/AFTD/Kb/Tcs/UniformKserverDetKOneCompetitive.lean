import AFTD.Prelude
import AFTD.Kb.Tcs.UniformKserverDetCompetitive
import AFTD.Kb.Tcs.UniformKserverDetAlgServes
import AFTD.Kb.Tcs.UniformKserverOfflineCost
import AFTD.Kb.Tcs.UniformKserverOpt
import AFTD.Kb.Tcs.UniformKserverDetSchedule
import AFTD.Kb.Tcs.UniformKserverIsSchedule
import AFTD.Kb.Tcs.UniformKserverDetCost

/-!
# uniform_kserver_det_k_one_competitive

Topic: online_algorithms   Node: adf28e4e05a7

Provenance: formalization of a published result. Source: arXiv:2610.37192 Sec. 6

For generalized 1-server on any family of uniform metric spaces M indexed by Fin 1 with decidable equality and any initial configuration a : ∀ i, M i, there exists a deterministic online algorithm A such that uniform_kserver_det_competitive 1 A a 1 holds.
-/

def uniform_kserver_det_k_one_alg {M : Fin 1 → Type*}
    (a : ∀ i, M i) : List (∀ i, M i) → (∀ i, M i) :=
  fun l => l.getLastD a

theorem uniform_kserver_det_k_one_sched_eq_rho {M : Fin 1 → Type*} (ρ sched : List (∀ i, M i))
    (h : uniform_kserver_is_schedule ρ sched) : sched = ρ := by
  rcases h with ⟨hlen, hserves⟩
  apply List.ext_getElem
  · exact hlen
  · intro i h1 h2
    have hzip : i < (sched.zip ρ).length := by
      rw [List.length_zip, hlen, min_self]
      exact h2
    have hmem : (sched[i], ρ[i]) ∈ sched.zip ρ := by
      have := List.getElem_mem hzip
      rwa [List.getElem_zip] at this
    have hserv := hserves (sched[i], ρ[i]) hmem
    ext j
    obtain ⟨k, hk⟩ := hserv
    have : j = k := Subsingleton.elim j k
    subst this
    exact hk

theorem uniform_kserver_det_k_one_rho_is_sched {M : Fin 1 → Type*} (ρ : List (∀ i, M i)) :
    uniform_kserver_is_schedule ρ ρ := by
  constructor
  · rfl
  · intro pair hpair
    use 0
    rw [List.mem_iff_getElem] at hpair
    obtain ⟨i, hi, rfl⟩ := hpair
    rw [List.getElem_zip]

theorem uniform_kserver_det_k_one_opt_eq {M : Fin 1 → Type*} [∀ i, DecidableEq (M i)]
    (a : ∀ i, M i) (ρ : List (∀ i, M i)) :
    uniform_kserver_opt 1 a ρ = uniform_kserver_offline_cost a ρ := by
  unfold uniform_kserver_opt
  have hset : {c : ℕ | ∃ sched, uniform_kserver_is_schedule ρ sched ∧ uniform_kserver_offline_cost a sched = c} =
      {uniform_kserver_offline_cost a ρ} := by
    ext c
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨sched, hsched, rfl⟩
      rw [uniform_kserver_det_k_one_sched_eq_rho ρ sched hsched]
    · rintro rfl
      exact ⟨ρ, uniform_kserver_det_k_one_rho_is_sched ρ, rfl⟩
  rw [hset]
  exact csInf_singleton _

theorem uniform_kserver_det_k_one_schedule_eq {M : Fin 1 → Type*}
    (a : ∀ i, M i) (ρ : List (∀ i, M i)) :
    uniform_kserver_det_schedule (uniform_kserver_det_k_one_alg a) ρ = ρ := by
  unfold uniform_kserver_det_schedule
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    dsimp [uniform_kserver_det_k_one_alg]
    rw [List.take_succ_eq_append_getElem h2]
    exact List.getLastD_concat

/-- The base case k = 1: generalized 1-server on uniform metrics is 1-competitive. -/
theorem uniform_kserver_det_k_one_competitive
    {M : Fin 1 → Type*} [∀ i, DecidableEq (M i)] (a : ∀ i, M i) :
    ∃ A, uniform_kserver_det_competitive 1 A a 1 := by
  use uniform_kserver_det_k_one_alg a
  unfold uniform_kserver_det_competitive
  constructor
  · intro ρ r
    use 0
    dsimp [uniform_kserver_det_k_one_alg]
    simp
  · use 0
    intro ρ
    unfold uniform_kserver_det_cost
    rw [uniform_kserver_det_k_one_schedule_eq a ρ]
    rw [uniform_kserver_det_k_one_opt_eq a ρ]
    linarith
