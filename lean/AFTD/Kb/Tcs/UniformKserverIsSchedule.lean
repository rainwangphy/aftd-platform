import AFTD.Prelude

/-!
# uniform_kserver_is_schedule

Topic: online_algorithms   Node: c576e9e520a8

Provenance: formalization of a published result. Source: scout/2610-37192-tight-bounds-for-randomized-generalized-k-server-on-uniform.md:340

For a natural number k, a family of spaces M indexed by Fin k, a list of requests ρ, and a list of configurations sched, sched is a valid schedule for ρ if sched and ρ have the same length and for every corresponding pair (x, r) in sched and ρ, x serves r (i.e. x i = r i for some i in Fin k).
-/

/-- An offline schedule is valid for request sequence ρ if it has the same length and each step serves the corresponding request. -/
def uniform_kserver_is_schedule {k : ℕ} {M : Fin k → Type*} (ρ : List (∀ i, M i)) (sched : List (∀ i, M i)) : Prop :=
  sched.length = ρ.length ∧ ∀ pair ∈ sched.zip ρ, ∃ i : Fin k, pair.1 i = pair.2 i
