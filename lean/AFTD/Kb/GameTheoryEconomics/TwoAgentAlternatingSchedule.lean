import AFTD.Prelude

/-!
# two_agent_alternating_schedule

Topic: fair_division   Node: d728e72669cd

Provenance: formalization of a published result. Source: Kalinowski et al., IJCAI 2013

Given the number of goods m : ℕ, the alternating drafting schedule of length m is the function from Fin m to Fin 2 sending each turn t : Fin m to the agent with index t.val % 2 in Fin 2.
-/

/-- The standard alternating two-agent drafting schedule of length m, sending t : Fin m to ⟨t.val % 2, _⟩ : Fin 2. -/
def two_agent_alternating_schedule (m : ℕ) : Fin m → Fin 2 :=
  fun t => ⟨t.val % 2, by omega⟩
