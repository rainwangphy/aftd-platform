import AFTD.Prelude

/-!
# arrival_hybrid_local_rule

Topic: algorithms   Node: 62393e32e191

Provenance: formalization of a published result. Source: scout/2611-33785-a-polynomial-time-algorithm-for-arrival.md:175

For types V and S, a period length dv : ℕ, a multiplicity vector mv : Sum V S → ℝ, an exact local routing rule rv : ℝ → Sum V S → ℝ, a restored period set Wv : Finset ℕ, and an input z : ℝ, arrival_hybrid_local_rule dv mv rv Wv z is the vector in Sum V S → ℝ equal to rv z if Nat.floor (z / (dv : ℝ)) ∈ Wv and (z / (dv : ℝ)) • mv otherwise.
-/

/-- Hybrid local outflow rule coinciding with exact rule on restored periods and linear average elsewhere. -/
noncomputable def arrival_hybrid_local_rule
    {V S : Type*} (dv : ℕ) (mv : Sum V S → ℝ) (rv : ℝ → Sum V S → ℝ) (Wv : Finset ℕ) (z : ℝ) :
    Sum V S → ℝ := if (Nat.floor (z / (dv : ℝ))) ∈ Wv then rv z else (z / (dv : ℝ)) • mv
