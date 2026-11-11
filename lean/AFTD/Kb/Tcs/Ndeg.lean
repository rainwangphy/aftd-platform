import AFTD.Prelude
import AFTD.Kb.Tcs.HasNondetPoly

/-!
# ndeg

Topic: circuits   Node: 11f066c962dc

Provenance: formalization of a published result. Source: arXiv:2611.11966 Def 11

The non-deterministic degree ndeg f of a Boolean function f : (Fin n → Bool) → Bool is the minimal natural number d such that f admits a non-deterministic polynomial of degree at most d, defined as sInf { d : ℕ | HasNondetPoly f d }.
-/

/-- The non-deterministic degree of a Boolean function f. -/
noncomputable def ndeg {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ := sInf { d : ℕ | HasNondetPoly f d }
