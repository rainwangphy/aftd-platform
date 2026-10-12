import AFTD.Prelude

/-!
# SavitchMidpoint

Topic: space_complexity   Node: d7956733a507

Provenance: formalization of a published result. Source: Savitch 1970, Section 2; Sipser, Theorem 8.5

The Savitch midpoint reachability relation family R_k(r) for a binary relation r on a type V, defined recursively: at step 0, u can reach v if u = v or r u v; at step k + 1, u can reach v if there exists an intermediate vertex w such that u can reach w and w can reach v at step k.
-/

/-- The k-step Savitch midpoint reachability relation: R_0 is the reflexive closure of r, and R_{k+1} is R_k ∘ R_k. -/
def SavitchMidpoint {V : Type*} (r : V → V → Prop) : ℕ → V → V → Prop
  | 0, u, v => u = v ∨ r u v
  | k + 1, u, v => ∃ w, SavitchMidpoint r k u w ∧ SavitchMidpoint r k w v
