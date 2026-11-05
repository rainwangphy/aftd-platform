import AFTD.Prelude

/-!
# is_ap_tile_step

Topic: combinatorics   Node: e3493e5de8a7

Provenance: formalization of a published result. Source: arXiv:2611.05321 Definition 1.4

Given a step parameter k : ℕ with [NeZero k], a finite subset A : Finset ℕ is an arithmetic progression tile with step k if for every residue class r : ZMod k, the number of elements a ∈ A such that (a : ZMod k) = r is 1.
-/

/-- A finite subset of ℕ is an arithmetic progression tile of step k if it contains exactly one representative of each residue class modulo k. -/
def is_ap_tile_step (k : ℕ) [NeZero k] (A : Finset ℕ) : Prop :=
  ∀ r : ZMod k, (A.filter (fun (a : ℕ) => (a : ZMod k) = r)).card = 1
