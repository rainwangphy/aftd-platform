import AFTD.Prelude
import AFTD.Kb.Tcs.UniformKserverOfflineCost
import AFTD.Kb.Tcs.UniformKserverIsSchedule

/-!
# uniform_kserver_opt

Topic: online_algorithms   Node: 8cf0dcaa7b3c

Provenance: formalization of a published result. Source: arXiv:2610.37192 Section 2

For a natural number k, a family of spaces M indexed by Fin k with decidable equality, an initial configuration a, and a list of requests ρ, uniform_kserver_opt k a ρ is the optimal offline cost, defined as the infimum in ℕ of the offline movement costs uniform_kserver_offline_cost a sched over all valid schedules sched for ρ.
-/

/-- The optimal offline cost for generalized k-server on uniform metrics. -/
noncomputable def uniform_kserver_opt (k : ℕ) {M : Fin k → Type*} [∀ i, DecidableEq (M i)]
    (a : ∀ i, M i) (ρ : List (∀ i, M i)) : ℕ := sInf {c : ℕ | ∃ sched, uniform_kserver_is_schedule ρ sched ∧ uniform_kserver_offline_cost a sched = c}
